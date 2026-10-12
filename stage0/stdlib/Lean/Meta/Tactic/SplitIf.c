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
lean_object* l_Lean_Meta_SplitKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Meta_SplitKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_SplitKind_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_Meta_SplitKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Meta_SplitKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Meta_SplitKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg(lean_object* v_ite_24_){
_start:
{
lean_inc(v_ite_24_);
return v_ite_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___redArg___boxed(lean_object* v_ite_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_SplitKind_ite_elim___redArg(v_ite_25_);
lean_dec(v_ite_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Meta_SplitKind_ite_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_ite_30_){
_start:
{
lean_inc(v_ite_30_);
return v_ite_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitKind_ite_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_ite_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_SplitKind_ite_elim(lean_box(0), v_t_28_, lean_box(0), v_ite_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_ite_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_ite_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_SplitKind_ite_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_ite_35_);
lean_dec(v_ite_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg(lean_object* v_match_38_){
_start:
{
lean_inc(v_match_38_);
return v_match_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___redArg___boxed(lean_object* v_match_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_SplitKind_match_elim___redArg(v_match_39_);
lean_dec(v_match_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Meta_SplitKind_match_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_match_44_){
_start:
{
lean_inc(v_match_44_);
return v_match_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitKind_match_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_match_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_SplitKind_match_elim(lean_box(0), v_t_42_, lean_box(0), v_match_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_match_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_match_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_SplitKind_match_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_match_49_);
lean_dec(v_match_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg(lean_object* v_both_52_){
_start:
{
lean_inc(v_both_52_);
return v_both_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___redArg___boxed(lean_object* v_both_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_SplitKind_both_elim___redArg(v_both_53_);
lean_dec(v_both_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Meta_SplitKind_both_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_both_58_){
_start:
{
lean_inc(v_both_58_);
return v_both_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitKind_both_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_both_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_SplitKind_both_elim(lean_box(0), v_t_56_, lean_box(0), v_both_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_both_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_both_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Meta_SplitKind_both_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_both_63_);
lean_dec(v_both_63_);
return v_res_65_;
}
}
uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t v_x_66_){
_start:
{
switch(v_x_66_)
{
case 0:
{
uint8_t v___x_67_; 
v___x_67_ = 1;
return v___x_67_;
}
case 2:
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
default: 
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SplitKind_considerIte_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_66_ = stack[0].m_num;
uint8_t v_res_70_;
v_res_70_ = l_Lean_Meta_SplitKind_considerIte(v_x_66_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object* v_x_71_){
_start:
{
uint8_t v_x_22__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_22__boxed_72_ = lean_unbox(v_x_71_);
v_res_73_ = l_Lean_Meta_SplitKind_considerIte(v_x_22__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t v_x_75_){
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
LEAN_EXPORT void l_Lean_Meta_SplitKind_considerMatch_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_75_ = stack[0].m_num;
uint8_t v_res_79_;
v_res_79_ = l_Lean_Meta_SplitKind_considerMatch(v_x_75_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object* v_x_80_){
_start:
{
uint8_t v_x_22__boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_x_22__boxed_81_ = lean_unbox(v_x_80_);
v_res_82_ = l_Lean_Meta_SplitKind_considerMatch(v_x_22__boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(lean_object* v_a_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
else
{
lean_object* v_key_87_; lean_object* v_tail_88_; uint8_t v___x_89_; 
v_key_87_ = lean_ctor_get(v_x_85_, 0);
v_tail_88_ = lean_ctor_get(v_x_85_, 2);
v___x_89_ = lean_expr_eqv(v_key_87_, v_a_84_);
if (v___x_89_ == 0)
{
v_x_85_ = v_tail_88_;
goto _start;
}
else
{
return v___x_89_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_84_ = stack[0].m_obj;
lean_object* v_x_85_ = stack[1].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_84_, v_x_85_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_92_, v_x_93_);
lean_dec(v_x_93_);
lean_dec_ref(v_a_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object* v_m_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_buckets_98_; lean_object* v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v_fold_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_buckets_98_ = lean_ctor_get(v_m_96_, 1);
v___x_99_ = lean_array_get_size(v_buckets_98_);
v___x_100_ = l_Lean_Expr_hash(v_a_97_);
v___x_101_ = 32ULL;
v___x_102_ = lean_uint64_shift_right(v___x_100_, v___x_101_);
v_fold_103_ = lean_uint64_xor(v___x_100_, v___x_102_);
v___x_104_ = 16ULL;
v___x_105_ = lean_uint64_shift_right(v_fold_103_, v___x_104_);
v___x_106_ = lean_uint64_xor(v_fold_103_, v___x_105_);
v___x_107_ = lean_uint64_to_usize(v___x_106_);
v___x_108_ = lean_usize_of_nat(v___x_99_);
v___x_109_ = ((size_t)1ULL);
v___x_110_ = lean_usize_sub(v___x_108_, v___x_109_);
v___x_111_ = lean_usize_land(v___x_107_, v___x_110_);
v___x_112_ = lean_array_uget_borrowed(v_buckets_98_, v___x_111_);
v___x_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_97_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_96_ = stack[0].m_obj;
lean_object* v_a_97_ = stack[1].m_obj;
uint8_t v_res_114_;
v_res_114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_96_, v_a_97_);
stack->m_num = v_res_114_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object* v_m_115_, lean_object* v_a_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_115_, v_a_116_);
lean_dec_ref(v_a_116_);
lean_dec_ref(v_m_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(lean_object* v_upperBound_127_, lean_object* v_args_128_, lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_lt(v_a_129_, v_upperBound_127_);
if (v___x_131_ == 0)
{
lean_dec(v_a_129_);
lean_inc_ref(v_b_130_);
return v_b_130_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = l_Lean_instInhabitedExpr;
v___x_133_ = lean_array_get_borrowed(v___x_132_, v_args_128_, v_a_129_);
v___x_134_ = l_Lean_Expr_hasLooseBVars(v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_a_129_, v___x_136_);
lean_dec(v_a_129_);
v_a_129_ = v___x_137_;
v_b_130_ = v___x_135_;
goto _start;
}
else
{
lean_object* v___x_139_; 
lean_dec(v_a_129_);
v___x_139_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2));
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_140_, lean_object* v_args_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_140_, v_args_141_, v_a_142_, v_b_143_);
lean_dec_ref(v_b_143_);
lean_dec_ref(v_args_141_);
lean_dec(v_upperBound_140_);
return v_res_144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v_dummy_146_; 
v___x_145_ = lean_box(0);
v_dummy_146_ = l_Lean_Expr_sort___override(v___x_145_);
return v_dummy_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object* v_env_153_, lean_object* v_ctx_154_, lean_object* v_e_155_){
_start:
{
lean_object* v_exceptionSet_156_; uint8_t v_kind_157_; lean_object* v_e_159_; uint8_t v___y_187_; uint8_t v___x_196_; 
v_exceptionSet_156_ = lean_ctor_get(v_ctx_154_, 0);
v_kind_157_ = lean_ctor_get_uint8(v_ctx_154_, sizeof(void*)*1);
v___x_196_ = l_Lean_Meta_SplitKind_considerIte(v_kind_157_);
if (v___x_196_ == 0)
{
goto v___jp_163_;
}
else
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_198_ = l_Lean_Expr_isAppOf(v_e_155_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_200_ = l_Lean_Expr_isAppOf(v_e_155_, v___x_199_);
if (v___x_200_ == 0)
{
goto v___jp_163_;
}
else
{
v___y_187_ = v___x_200_;
goto v___jp_186_;
}
}
else
{
v___y_187_ = v___x_198_;
goto v___jp_186_;
}
}
v___jp_158_:
{
uint8_t v___x_160_; 
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_exceptionSet_156_, v_e_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v_e_159_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
lean_dec_ref(v_e_159_);
v___x_162_ = lean_box(0);
return v___x_162_;
}
}
v___jp_163_:
{
uint8_t v___x_164_; 
v___x_164_ = l_Lean_Meta_SplitKind_considerMatch(v_kind_157_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_dec_ref(v_e_155_);
lean_dec_ref(v_env_153_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_153_, v_e_155_);
if (lean_obj_tag(v___x_166_) == 1)
{
lean_object* v_val_167_; lean_object* v_numDiscrs_168_; lean_object* v_nargs_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_dummy_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_args_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_fst_179_; 
v_val_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_166_, 1);
v_numDiscrs_168_ = lean_ctor_get(v_val_167_, 1);
v_nargs_169_ = l_Lean_Expr_getAppNumArgs(v_e_155_);
v___x_170_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_167_);
v___x_171_ = lean_nat_add(v___x_170_, v_numDiscrs_168_);
v_dummy_172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
lean_inc(v_nargs_169_);
v___x_173_ = lean_mk_array(v_nargs_169_, v_dummy_172_);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_sub(v_nargs_169_, v___x_174_);
lean_dec(v_nargs_169_);
lean_inc_ref(v_e_155_);
v_args_176_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_155_, v___x_173_, v___x_175_);
v___x_177_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v___x_171_, v_args_176_, v___x_170_, v___x_177_);
lean_dec(v___x_171_);
v_fst_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_fst_179_);
lean_dec_ref(v___x_178_);
if (lean_obj_tag(v_fst_179_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = lean_array_get_size(v_args_176_);
lean_dec_ref(v_args_176_);
v___x_181_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_167_);
lean_dec(v_val_167_);
v___x_182_ = lean_nat_sub(v___x_180_, v___x_181_);
lean_dec(v___x_181_);
v___x_183_ = l_Lean_Expr_getBoundedAppFn(v___x_182_, v_e_155_);
lean_dec_ref(v_e_155_);
v_e_159_ = v___x_183_;
goto v___jp_158_;
}
else
{
lean_object* v_val_184_; 
lean_dec_ref(v_args_176_);
lean_dec(v_val_167_);
lean_dec_ref(v_e_155_);
v_val_184_ = lean_ctor_get(v_fst_179_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v_fst_179_, 1);
return v_val_184_;
}
}
else
{
lean_object* v___x_185_; 
lean_dec(v___x_166_);
lean_dec_ref(v_e_155_);
v___x_185_ = lean_box(0);
return v___x_185_;
}
}
}
v___jp_186_:
{
lean_object* v_numArgs_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_numArgs_188_ = l_Lean_Expr_getAppNumArgs(v_e_155_);
v___x_189_ = lean_unsigned_to_nat(5u);
v___x_190_ = lean_nat_dec_le(v___x_189_, v_numArgs_188_);
if (v___x_190_ == 0)
{
lean_dec(v_numArgs_188_);
goto v___jp_163_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(3u);
v___x_192_ = l_Lean_Expr_getRevArg_x21(v_e_155_, v___x_191_);
v___x_193_ = l_Lean_Expr_hasLooseBVars(v___x_192_);
lean_dec_ref(v___x_192_);
if (v___x_193_ == 0)
{
if (v___y_187_ == 0)
{
lean_dec(v_numArgs_188_);
goto v___jp_163_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v_env_153_);
v___x_194_ = lean_nat_sub(v_numArgs_188_, v___x_189_);
lean_dec(v_numArgs_188_);
v___x_195_ = l_Lean_Expr_getBoundedAppFn(v___x_194_, v_e_155_);
lean_dec_ref(v_e_155_);
v_e_159_ = v___x_195_;
goto v___jp_158_;
}
}
else
{
lean_dec(v_numArgs_188_);
goto v___jp_163_;
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* v_00_u03b2_205_, lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_206_, v_a_207_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_206_ = stack[1].m_obj;
lean_object* v_a_207_ = stack[2].m_obj;
uint8_t v_res_209_;
v_res_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_box(0), v_m_206_, v_a_207_);
stack->m_num = v_res_209_;
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_object* v_00_u03b2_231_, lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_232_, v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_232_ = stack[1].m_obj;
lean_object* v_x_233_ = stack[2].m_obj;
uint8_t v_res_235_;
v_res_235_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(lean_box(0), v_a_232_, v_x_233_);
stack->m_num = v_res_235_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_236_, lean_object* v_a_237_, lean_object* v_x_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_236_, v_a_237_, v_x_238_);
lean_dec(v_x_238_);
lean_dec_ref(v_a_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* v_e_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___f_248_; lean_object* v___f_249_; uint8_t v___x_250_; 
v___f_248_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_249_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_245_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_248_, v___f_249_, v_a_246_, v_e_245_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_251_ = lean_box(0);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_248_, v___f_249_, v_a_246_, v_e_245_, v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v_e_245_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_a_246_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_FindSplitImpl_checkVisited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_245_ = stack[0].m_obj;
lean_object* v_a_246_ = stack[1].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_245_, v_a_246_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_260_, v_a_261_);
return v_res_263_;
}
}
lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* v_e_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___f_272_; lean_object* v___f_273_; uint8_t v___x_274_; 
v___f_272_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0));
v___f_273_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1));
lean_inc_ref(v_e_264_);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_272_, v___f_273_, v_a_266_, v_e_264_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_275_ = lean_box(0);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_272_, v___f_273_, v_a_266_, v_e_264_, v___x_275_);
v___x_277_ = ((lean_object*)(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2));
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v_e_264_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_a_266_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_FindSplitImpl_checkVisited_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_264_ = stack[0].m_obj;
lean_object* v_a_265_ = stack[1].m_obj;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_a_270_ = stack[6].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_FindSplitImpl_checkVisited(v_e_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec_ref(v_a_285_);
return v_res_292_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
else
{
lean_object* v_key_296_; lean_object* v_tail_297_; size_t v___x_298_; size_t v___x_299_; uint8_t v___x_300_; 
v_key_296_ = lean_ctor_get(v_x_294_, 0);
v_tail_297_ = lean_ctor_get(v_x_294_, 2);
v___x_298_ = lean_ptr_addr(v_key_296_);
v___x_299_ = lean_ptr_addr(v_a_293_);
v___x_300_ = lean_usize_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
v_x_294_ = v_tail_297_;
goto _start;
}
else
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_293_ = stack[0].m_obj;
lean_object* v_x_294_ = stack[1].m_obj;
uint8_t v_res_302_;
v_res_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_293_, v_x_294_);
stack->m_num = v_res_302_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_303_, v_x_304_);
lean_dec(v_x_304_);
lean_dec_ref(v_a_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
return v_x_307_;
}
else
{
lean_object* v_key_309_; lean_object* v_value_310_; lean_object* v_tail_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_337_; 
v_key_309_ = lean_ctor_get(v_x_308_, 0);
v_value_310_ = lean_ctor_get(v_x_308_, 1);
v_tail_311_ = lean_ctor_get(v_x_308_, 2);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_337_ == 0)
{
v___x_313_ = v_x_308_;
v_isShared_314_ = v_isSharedCheck_337_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_tail_311_);
lean_inc(v_value_310_);
lean_inc(v_key_309_);
lean_dec(v_x_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_337_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; size_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v_fold_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_315_ = lean_array_get_size(v_x_307_);
v___x_316_ = lean_ptr_addr(v_key_309_);
v___x_317_ = lean_usize_to_uint64(v___x_316_);
v___x_318_ = 11ULL;
v___x_319_ = lean_uint64_mix_hash(v___x_317_, v___x_318_);
v___x_320_ = 32ULL;
v___x_321_ = lean_uint64_shift_right(v___x_319_, v___x_320_);
v_fold_322_ = lean_uint64_xor(v___x_319_, v___x_321_);
v___x_323_ = 16ULL;
v___x_324_ = lean_uint64_shift_right(v_fold_322_, v___x_323_);
v___x_325_ = lean_uint64_xor(v_fold_322_, v___x_324_);
v___x_326_ = lean_uint64_to_usize(v___x_325_);
v___x_327_ = lean_usize_of_nat(v___x_315_);
v___x_328_ = ((size_t)1ULL);
v___x_329_ = lean_usize_sub(v___x_327_, v___x_328_);
v___x_330_ = lean_usize_land(v___x_326_, v___x_329_);
v___x_331_ = lean_array_uget_borrowed(v_x_307_, v___x_330_);
lean_inc(v___x_331_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 2, v___x_331_);
v___x_333_ = v___x_313_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_key_309_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_value_310_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v___x_331_);
v___x_333_ = v_reuseFailAlloc_336_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_uset(v_x_307_, v___x_330_, v___x_333_);
v_x_307_ = v___x_334_;
v_x_308_ = v_tail_311_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_338_, lean_object* v_source_339_, lean_object* v_target_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_array_get_size(v_source_339_);
v___x_342_ = lean_nat_dec_lt(v_i_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec_ref(v_source_339_);
lean_dec(v_i_338_);
return v_target_340_;
}
else
{
lean_object* v_es_343_; lean_object* v___x_344_; lean_object* v_source_345_; lean_object* v_target_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_es_343_ = lean_array_fget(v_source_339_, v_i_338_);
v___x_344_ = lean_box(0);
v_source_345_ = lean_array_fset(v_source_339_, v_i_338_, v___x_344_);
v_target_346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_340_, v_es_343_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_i_338_, v___x_347_);
lean_dec(v_i_338_);
v_i_338_ = v___x_348_;
v_source_339_ = v_source_345_;
v_target_340_ = v_target_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_nbuckets_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_351_ = lean_array_get_size(v_data_350_);
v___x_352_ = lean_unsigned_to_nat(2u);
v_nbuckets_353_ = lean_nat_mul(v___x_351_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_box(0);
v___x_356_ = lean_mk_array(v_nbuckets_353_, v___x_355_);
v___x_357_ = lean_array_propagate_mark(v_data_350_, v___x_356_);
v___x_358_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v___x_354_, v_data_350_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(lean_object* v_m_359_, lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
lean_object* v_size_362_; lean_object* v_buckets_363_; lean_object* v___x_364_; size_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v_fold_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v_bkt_380_; uint8_t v___x_381_; 
v_size_362_ = lean_ctor_get(v_m_359_, 0);
v_buckets_363_ = lean_ctor_get(v_m_359_, 1);
v___x_364_ = lean_array_get_size(v_buckets_363_);
v___x_365_ = lean_ptr_addr(v_a_360_);
v___x_366_ = lean_usize_to_uint64(v___x_365_);
v___x_367_ = 11ULL;
v___x_368_ = lean_uint64_mix_hash(v___x_366_, v___x_367_);
v___x_369_ = 32ULL;
v___x_370_ = lean_uint64_shift_right(v___x_368_, v___x_369_);
v_fold_371_ = lean_uint64_xor(v___x_368_, v___x_370_);
v___x_372_ = 16ULL;
v___x_373_ = lean_uint64_shift_right(v_fold_371_, v___x_372_);
v___x_374_ = lean_uint64_xor(v_fold_371_, v___x_373_);
v___x_375_ = lean_uint64_to_usize(v___x_374_);
v___x_376_ = lean_usize_of_nat(v___x_364_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_sub(v___x_376_, v___x_377_);
v___x_379_ = lean_usize_land(v___x_375_, v___x_378_);
v_bkt_380_ = lean_array_uget_borrowed(v_buckets_363_, v___x_379_);
v___x_381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_360_, v_bkt_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_402_; 
lean_inc_ref(v_buckets_363_);
lean_inc(v_size_362_);
v_isSharedCheck_402_ = !lean_is_exclusive(v_m_359_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_403_ = lean_ctor_get(v_m_359_, 1);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_m_359_, 0);
lean_dec(v_unused_404_);
v___x_383_ = v_m_359_;
v_isShared_384_ = v_isSharedCheck_402_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_m_359_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_402_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v_size_x27_386_; lean_object* v___x_387_; lean_object* v_buckets_x27_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v_size_x27_386_ = lean_nat_add(v_size_362_, v___x_385_);
lean_dec(v_size_362_);
lean_inc(v_bkt_380_);
v___x_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_387_, 0, v_a_360_);
lean_ctor_set(v___x_387_, 1, v_b_361_);
lean_ctor_set(v___x_387_, 2, v_bkt_380_);
v_buckets_x27_388_ = lean_array_uset(v_buckets_363_, v___x_379_, v___x_387_);
v___x_389_ = lean_unsigned_to_nat(4u);
v___x_390_ = lean_nat_mul(v_size_x27_386_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_nat_div(v___x_390_, v___x_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_array_get_size(v_buckets_x27_388_);
v___x_394_ = lean_nat_dec_le(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v_val_395_; lean_object* v___x_397_; 
v_val_395_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_buckets_x27_388_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_val_395_);
lean_ctor_set(v___x_383_, 0, v_size_x27_386_);
v___x_397_ = v___x_383_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_val_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_object* v___x_400_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_buckets_x27_388_);
lean_ctor_set(v___x_383_, 0, v_size_x27_386_);
v___x_400_ = v___x_383_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_buckets_x27_388_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_dec(v_b_361_);
lean_dec_ref(v_a_360_);
return v_m_359_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(lean_object* v_m_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_buckets_407_; lean_object* v___x_408_; size_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v_fold_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_buckets_407_ = lean_ctor_get(v_m_405_, 1);
v___x_408_ = lean_array_get_size(v_buckets_407_);
v___x_409_ = lean_ptr_addr(v_a_406_);
v___x_410_ = lean_usize_to_uint64(v___x_409_);
v___x_411_ = 11ULL;
v___x_412_ = lean_uint64_mix_hash(v___x_410_, v___x_411_);
v___x_413_ = 32ULL;
v___x_414_ = lean_uint64_shift_right(v___x_412_, v___x_413_);
v_fold_415_ = lean_uint64_xor(v___x_412_, v___x_414_);
v___x_416_ = 16ULL;
v___x_417_ = lean_uint64_shift_right(v_fold_415_, v___x_416_);
v___x_418_ = lean_uint64_xor(v_fold_415_, v___x_417_);
v___x_419_ = lean_uint64_to_usize(v___x_418_);
v___x_420_ = lean_usize_of_nat(v___x_408_);
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_sub(v___x_420_, v___x_421_);
v___x_423_ = lean_usize_land(v___x_419_, v___x_422_);
v___x_424_ = lean_array_uget_borrowed(v_buckets_407_, v___x_423_);
v___x_425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_406_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_405_ = stack[0].m_obj;
lean_object* v_a_406_ = stack[1].m_obj;
uint8_t v_res_426_;
v_res_426_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_405_, v_a_406_);
stack->m_num = v_res_426_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(lean_object* v_m_427_, lean_object* v_a_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_427_, v_a_428_);
lean_dec_ref(v_a_428_);
lean_dec_ref(v_m_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object* v_e_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; uint8_t v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_a_433_, v_e_431_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_env_474_; lean_object* v___x_475_; 
v___x_471_ = lean_box(0);
lean_inc_ref_n(v_e_431_, 2);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_433_, v_e_431_, v___x_471_);
v___x_473_ = lean_st_ref_get(v_a_437_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_env_474_);
lean_dec(v___x_473_);
v___x_475_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_474_, v_a_432_, v_e_431_);
if (lean_obj_tag(v___x_475_) == 1)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec_ref(v_e_431_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_472_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; 
lean_dec(v___x_475_);
v___x_478_ = l_Lean_Expr_hasLooseBVars(v_e_431_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_inc_ref(v_e_431_);
v___x_479_ = l_Lean_Meta_isProof(v_e_431_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_unbox(v_a_480_);
lean_dec(v_a_480_);
if (v___x_484_ == 0)
{
lean_del_object(v___x_482_);
v___y_440_ = v_a_432_;
v___y_441_ = v___x_472_;
v___y_442_ = v_a_434_;
v___y_443_ = v_a_435_;
v___y_444_ = v_a_436_;
v___y_445_ = v_a_437_;
goto v___jp_439_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec_ref(v_e_431_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_472_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_486_);
v___x_488_ = v___x_482_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v___x_472_);
lean_dec_ref(v_e_431_);
v_a_491_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_479_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_479_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
v___y_440_ = v_a_432_;
v___y_441_ = v___x_472_;
v___y_442_ = v_a_434_;
v___y_443_ = v_a_435_;
v___y_444_ = v_a_436_;
v___y_445_ = v_a_437_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v_e_431_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_a_433_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
v___jp_439_:
{
switch(lean_obj_tag(v_e_431_))
{
case 6:
{
lean_object* v_body_446_; 
v_body_446_ = lean_ctor_get(v_e_431_, 2);
lean_inc_ref(v_body_446_);
lean_dec_ref_known(v_e_431_, 3);
v_e_431_ = v_body_446_;
v_a_432_ = v___y_440_;
v_a_433_ = v___y_441_;
v_a_434_ = v___y_442_;
v_a_435_ = v___y_443_;
v_a_436_ = v___y_444_;
v_a_437_ = v___y_445_;
goto _start;
}
case 11:
{
lean_object* v_struct_448_; 
v_struct_448_ = lean_ctor_get(v_e_431_, 2);
lean_inc_ref(v_struct_448_);
lean_dec_ref_known(v_e_431_, 3);
v_e_431_ = v_struct_448_;
v_a_432_ = v___y_440_;
v_a_433_ = v___y_441_;
v_a_434_ = v___y_442_;
v_a_435_ = v___y_443_;
v_a_436_ = v___y_444_;
v_a_437_ = v___y_445_;
goto _start;
}
case 10:
{
lean_object* v_expr_450_; 
v_expr_450_ = lean_ctor_get(v_e_431_, 1);
lean_inc_ref(v_expr_450_);
lean_dec_ref_known(v_e_431_, 2);
v_e_431_ = v_expr_450_;
v_a_432_ = v___y_440_;
v_a_433_ = v___y_441_;
v_a_434_ = v___y_442_;
v_a_435_ = v___y_443_;
v_a_436_ = v___y_444_;
v_a_437_ = v___y_445_;
goto _start;
}
case 7:
{
lean_object* v_binderType_452_; lean_object* v_body_453_; lean_object* v___x_454_; 
v_binderType_452_ = lean_ctor_get(v_e_431_, 1);
lean_inc_ref(v_binderType_452_);
v_body_453_ = lean_ctor_get(v_e_431_, 2);
lean_inc_ref(v_body_453_);
lean_dec_ref_known(v_e_431_, 3);
v___x_454_ = l_Lean_Meta_FindSplitImpl_visit(v_binderType_452_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v_fst_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_fst_456_ = lean_ctor_get(v_a_455_, 0);
if (lean_obj_tag(v_fst_456_) == 0)
{
lean_object* v_snd_457_; 
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v_snd_457_ = lean_ctor_get(v_a_455_, 1);
lean_inc(v_snd_457_);
lean_dec(v_a_455_);
v_e_431_ = v_body_453_;
v_a_432_ = v___y_440_;
v_a_433_ = v_snd_457_;
v_a_434_ = v___y_442_;
v_a_435_ = v___y_443_;
v_a_436_ = v___y_444_;
v_a_437_ = v___y_445_;
goto _start;
}
else
{
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
case 8:
{
lean_object* v_value_459_; lean_object* v_body_460_; lean_object* v___x_461_; 
v_value_459_ = lean_ctor_get(v_e_431_, 2);
lean_inc_ref(v_value_459_);
v_body_460_ = lean_ctor_get(v_e_431_, 3);
lean_inc_ref(v_body_460_);
lean_dec_ref_known(v_e_431_, 4);
v___x_461_ = l_Lean_Meta_FindSplitImpl_visit(v_value_459_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v_fst_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_fst_463_ = lean_ctor_get(v_a_462_, 0);
if (lean_obj_tag(v_fst_463_) == 0)
{
lean_object* v_snd_464_; 
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v_snd_464_ = lean_ctor_get(v_a_462_, 1);
lean_inc(v_snd_464_);
lean_dec(v_a_462_);
v_e_431_ = v_body_460_;
v_a_432_ = v___y_440_;
v_a_433_ = v_snd_464_;
v_a_434_ = v___y_442_;
v_a_435_ = v___y_443_;
v_a_436_ = v___y_444_;
v_a_437_ = v___y_445_;
goto _start;
}
else
{
lean_dec_ref(v_body_460_);
return v___x_461_;
}
}
else
{
lean_dec_ref(v_body_460_);
return v___x_461_;
}
}
case 5:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_431_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_466_;
}
default: 
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_e_431_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___y_441_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_FindSplitImpl_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_431_ = stack[0].m_obj;
lean_object* v_a_432_ = stack[1].m_obj;
lean_object* v_a_433_ = stack[2].m_obj;
lean_object* v_a_434_ = stack[3].m_obj;
lean_object* v_a_435_ = stack[4].m_obj;
lean_object* v_a_436_ = stack[5].m_obj;
lean_object* v_a_437_ = stack[6].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Meta_FindSplitImpl_visit(v_e_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
stack->m_obj
 = v_res_502_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object* v_upperBound_503_, lean_object* v_args_504_, lean_object* v_info_505_, lean_object* v_a_506_, lean_object* v_b_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_a_516_; lean_object* v_snd_517_; lean_object* v_a_521_; lean_object* v_snd_522_; uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_lt(v_a_506_, v_upperBound_503_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_a_506_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_b_507_);
lean_ctor_set(v___x_527_, 1, v___y_509_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v_paramInfo_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
lean_dec_ref(v_b_507_);
v_paramInfo_529_ = lean_ctor_get(v_info_505_, 0);
v___x_530_ = lean_box(0);
v___x_531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_532_ = lean_array_fget_borrowed(v_args_504_, v_a_506_);
v___x_533_ = lean_array_get_size(v_paramInfo_529_);
v___x_534_ = lean_nat_dec_lt(v_a_506_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_inc(v___x_532_);
v___x_535_ = l_Lean_Meta_FindSplitImpl_visit(v___x_532_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_fst_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v_fst_537_ = lean_ctor_get(v_a_536_, 0);
if (lean_obj_tag(v_fst_537_) == 1)
{
lean_object* v_snd_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
lean_inc_ref(v_fst_537_);
lean_dec(v_a_506_);
v_snd_538_ = lean_ctor_get(v_a_536_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v_a_536_, 0);
lean_dec(v_unused_547_);
v___x_540_ = v_a_536_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snd_538_);
lean_dec(v_a_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_fst_537_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_530_);
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_530_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_516_ = v___x_544_;
v_snd_517_ = v_snd_538_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v_snd_548_; 
v_snd_548_ = lean_ctor_get(v_a_536_, 1);
lean_inc(v_snd_548_);
lean_dec(v_a_536_);
v_a_521_ = v___x_531_;
v_snd_522_ = v_snd_548_;
goto v___jp_520_;
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_506_);
v_a_549_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_535_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_535_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v___x_557_; uint8_t v_isProp_558_; 
v___x_557_ = lean_array_fget_borrowed(v_paramInfo_529_, v_a_506_);
v_isProp_558_ = lean_ctor_get_uint8(v___x_557_, sizeof(void*)*1 + 2);
if (v_isProp_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_557_);
if (v___x_559_ == 0)
{
v_a_521_ = v___x_531_;
v_snd_522_ = v___y_509_;
goto v___jp_520_;
}
else
{
lean_object* v___x_560_; 
lean_inc(v___x_532_);
v___x_560_ = l_Lean_Meta_FindSplitImpl_visit(v___x_532_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_fst_562_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v_fst_562_ = lean_ctor_get(v_a_561_, 0);
if (lean_obj_tag(v_fst_562_) == 1)
{
lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
lean_inc_ref(v_fst_562_);
lean_dec(v_a_506_);
v_snd_563_ = lean_ctor_get(v_a_561_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_a_561_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v_a_561_, 0);
lean_dec(v_unused_572_);
v___x_565_ = v_a_561_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_dec(v_a_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v_fst_562_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_530_);
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_530_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v_a_516_ = v___x_569_;
v_snd_517_ = v_snd_563_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v_snd_573_; 
v_snd_573_ = lean_ctor_get(v_a_561_, 1);
lean_inc(v_snd_573_);
lean_dec(v_a_561_);
v_a_521_ = v___x_531_;
v_snd_522_ = v_snd_573_;
goto v___jp_520_;
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_a_506_);
v_a_574_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_560_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_560_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
else
{
v_a_521_ = v___x_531_;
v_snd_522_ = v___y_509_;
goto v___jp_520_;
}
}
}
v___jp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_516_);
lean_ctor_set(v___x_518_, 1, v_snd_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
v___jp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_a_506_, v___x_523_);
lean_dec(v_a_506_);
lean_inc_ref(v_a_521_);
v_a_506_ = v___x_524_;
v_b_507_ = v_a_521_;
v___y_509_ = v_snd_522_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_503_ = stack[0].m_obj;
lean_object* v_args_504_ = stack[1].m_obj;
lean_object* v_info_505_ = stack[2].m_obj;
lean_object* v_a_506_ = stack[3].m_obj;
lean_object* v_b_507_ = stack[4].m_obj;
lean_object* v___y_508_ = stack[5].m_obj;
lean_object* v___y_509_ = stack[6].m_obj;
lean_object* v___y_510_ = stack[7].m_obj;
lean_object* v___y_511_ = stack[8].m_obj;
lean_object* v___y_512_ = stack[9].m_obj;
lean_object* v___y_513_ = stack[10].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_503_, v_args_504_, v_info_505_, v_a_506_, v_b_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
stack->m_obj
 = v_res_582_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_info_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; 
if (lean_obj_tag(v_x_587_) == 5)
{
lean_object* v_fn_639_; lean_object* v_arg_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_fn_639_ = lean_ctor_get(v_x_587_, 0);
lean_inc_ref(v_fn_639_);
v_arg_640_ = lean_ctor_get(v_x_587_, 1);
lean_inc_ref(v_arg_640_);
lean_dec_ref_known(v_x_587_, 2);
v___x_641_ = lean_array_set(v_x_588_, v_x_589_, v_arg_640_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_sub(v_x_589_, v___x_642_);
lean_dec(v_x_589_);
v_x_587_ = v_fn_639_;
v_x_588_ = v___x_641_;
v_x_589_ = v___x_643_;
goto _start;
}
else
{
uint8_t v___x_645_; 
lean_dec(v_x_589_);
v___x_645_ = l_Lean_Expr_hasLooseBVars(v_x_587_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
lean_inc_ref(v_x_587_);
v___x_647_ = l_Lean_Meta_getFunInfo(v_x_587_, v___x_646_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v_info_598_ = v_a_648_;
v___y_599_ = v___y_590_;
v___y_600_ = v___y_591_;
v___y_601_ = v___y_592_;
v___y_602_ = v___y_593_;
v___y_603_ = v___y_594_;
v___y_604_ = v___y_595_;
goto v___jp_597_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___y_591_);
lean_dec_ref(v_x_588_);
lean_dec_ref(v_x_587_);
v_a_649_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_647_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v___x_657_; 
v___x_657_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1));
v_info_598_ = v___x_657_;
v___y_599_ = v___y_590_;
v___y_600_ = v___y_591_;
v___y_601_ = v___y_592_;
v___y_602_ = v___y_593_;
v___y_603_ = v___y_594_;
v___y_604_ = v___y_595_;
goto v___jp_597_;
}
}
v___jp_597_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_array_get_size(v_x_588_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0));
v___x_608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v___x_605_, v_x_588_, v_info_598_, v___x_606_, v___x_607_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec_ref(v_info_598_);
lean_dec_ref(v_x_588_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_630_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_630_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_630_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_630_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_fst_613_; lean_object* v_fst_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_628_; 
v_fst_613_ = lean_ctor_get(v_a_609_, 0);
lean_inc(v_fst_613_);
v_fst_614_ = lean_ctor_get(v_fst_613_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_fst_613_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_fst_613_, 1);
lean_dec(v_unused_629_);
v___x_616_ = v_fst_613_;
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_fst_614_);
lean_dec(v_fst_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
if (lean_obj_tag(v_fst_614_) == 0)
{
lean_object* v_snd_618_; lean_object* v___x_619_; 
lean_del_object(v___x_616_);
lean_del_object(v___x_611_);
v_snd_618_ = lean_ctor_get(v_a_609_, 1);
lean_inc(v_snd_618_);
lean_dec(v_a_609_);
v___x_619_ = l_Lean_Meta_FindSplitImpl_visit(v_x_587_, v___y_599_, v_snd_618_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
return v___x_619_;
}
else
{
lean_object* v_snd_620_; lean_object* v_val_621_; lean_object* v___x_623_; 
lean_dec_ref(v_x_587_);
v_snd_620_ = lean_ctor_get(v_a_609_, 1);
lean_inc(v_snd_620_);
lean_dec(v_a_609_);
v_val_621_ = lean_ctor_get(v_fst_614_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v_fst_614_, 1);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_snd_620_);
lean_ctor_set(v___x_616_, 0, v_val_621_);
v___x_623_ = v___x_616_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_val_621_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_snd_620_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_623_);
v___x_625_ = v___x_611_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_x_587_);
v_a_631_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_608_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_608_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_587_ = stack[0].m_obj;
lean_object* v_x_588_ = stack[1].m_obj;
lean_object* v_x_589_ = stack[2].m_obj;
lean_object* v___y_590_ = stack[3].m_obj;
lean_object* v___y_591_ = stack[4].m_obj;
lean_object* v___y_592_ = stack[5].m_obj;
lean_object* v___y_593_ = stack[6].m_obj;
lean_object* v___y_594_ = stack[7].m_obj;
lean_object* v___y_595_ = stack[8].m_obj;
lean_object* v_res_658_;
v_res_658_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_587_, v_x_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
stack->m_obj
 = v_res_658_;
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_dummy_667_; lean_object* v_nargs_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_dummy_667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
v_nargs_668_ = l_Lean_Expr_getAppNumArgs(v_e_659_);
lean_inc(v_nargs_668_);
v___x_669_ = lean_mk_array(v_nargs_668_, v_dummy_667_);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_sub(v_nargs_668_, v___x_670_);
lean_dec(v_nargs_668_);
v___x_672_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_e_659_, v___x_669_, v___x_671_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
return v___x_672_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_659_ = stack[0].m_obj;
lean_object* v_a_660_ = stack[1].m_obj;
lean_object* v_a_661_ = stack[2].m_obj;
lean_object* v_a_662_ = stack[3].m_obj;
lean_object* v_a_663_ = stack[4].m_obj;
lean_object* v_a_664_ = stack[5].m_obj;
lean_object* v_a_665_ = stack[6].m_obj;
lean_object* v_res_673_;
v_res_673_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_a_675_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_683_, v_x_684_, v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_686_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_694_, lean_object* v_args_695_, lean_object* v_info_696_, lean_object* v_a_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_694_, v_args_695_, v_info_696_, v_a_697_, v_b_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v_info_696_);
lean_dec_ref(v_args_695_);
lean_dec(v_upperBound_694_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_FindSplitImpl_visit(v_e_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_708_);
return v_res_715_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object* v_upperBound_716_, lean_object* v_args_717_, lean_object* v_info_718_, lean_object* v_inst_719_, lean_object* v_R_720_, lean_object* v_a_721_, lean_object* v_b_722_, lean_object* v_c_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_716_, v_args_717_, v_info_718_, v_a_721_, v_b_722_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_716_ = stack[0].m_obj;
lean_object* v_args_717_ = stack[1].m_obj;
lean_object* v_info_718_ = stack[2].m_obj;
lean_object* v_a_721_ = stack[5].m_obj;
lean_object* v_b_722_ = stack[6].m_obj;
lean_object* v___y_724_ = stack[8].m_obj;
lean_object* v___y_725_ = stack[9].m_obj;
lean_object* v___y_726_ = stack[10].m_obj;
lean_object* v___y_727_ = stack[11].m_obj;
lean_object* v___y_728_ = stack[12].m_obj;
lean_object* v___y_729_ = stack[13].m_obj;
lean_object* v_res_732_;
v_res_732_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_716_, v_args_717_, v_info_718_, lean_box(0), lean_box(0), v_a_721_, v_b_722_, lean_box(0), v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
stack->m_obj
 = v_res_732_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object* v_upperBound_733_, lean_object* v_args_734_, lean_object* v_info_735_, lean_object* v_inst_736_, lean_object* v_R_737_, lean_object* v_a_738_, lean_object* v_b_739_, lean_object* v_c_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_733_, v_args_734_, v_info_735_, v_inst_736_, v_R_737_, v_a_738_, v_b_739_, v_c_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v_info_735_);
lean_dec_ref(v_args_734_);
lean_dec(v_upperBound_733_);
return v_res_748_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_object* v_00_u03b2_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_750_, v_a_751_);
return v___x_752_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_750_ = stack[1].m_obj;
lean_object* v_a_751_ = stack[2].m_obj;
uint8_t v_res_753_;
v_res_753_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(lean_box(0), v_m_750_, v_a_751_);
stack->m_num = v_res_753_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(lean_object* v_00_u03b2_754_, lean_object* v_m_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(v_00_u03b2_754_, v_m_755_, v_a_756_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_m_755_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4(lean_object* v_00_u03b2_759_, lean_object* v_m_760_, lean_object* v_a_761_, lean_object* v_b_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_760_, v_a_761_, v_b_762_);
return v___x_763_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_object* v_00_u03b2_764_, lean_object* v_a_765_, lean_object* v_x_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_765_ = stack[1].m_obj;
lean_object* v_x_766_ = stack[2].m_obj;
uint8_t v_res_768_;
v_res_768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(lean_box(0), v_a_765_, v_x_766_);
stack->m_num = v_res_768_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_769_, lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(v_00_u03b2_769_, v_a_770_, v_x_771_);
lean_dec(v_x_771_);
lean_dec_ref(v_a_770_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(lean_object* v_00_u03b2_774_, lean_object* v_data_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_data_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_777_, lean_object* v_i_778_, lean_object* v_source_779_, lean_object* v_target_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v_i_778_, v_source_779_, v_target_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_783_, v_x_784_);
return v___x_785_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(64u);
v___x_787_ = l_Lean_mkPtrSet___redArg(v___x_786_);
return v___x_787_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t v_kind_788_, lean_object* v_exceptionSet_789_, lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_796_, 0, v_exceptionSet_789_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*1, v_kind_788_);
v___x_797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_798_ = l_Lean_Meta_FindSplitImpl_visit(v_e_790_, v___x_796_, v___x_797_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec_ref_known(v___x_796_, 1);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_807_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_fst_803_; lean_object* v___x_805_; 
v_fst_803_ = lean_ctor_get(v_a_799_, 0);
lean_inc(v_fst_803_);
lean_dec(v_a_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_fst_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_fst_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_798_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_798_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_788_ = stack[0].m_num;
lean_object* v_exceptionSet_789_ = stack[1].m_obj;
lean_object* v_e_790_ = stack[2].m_obj;
lean_object* v_a_791_ = stack[3].m_obj;
lean_object* v_a_792_ = stack[4].m_obj;
lean_object* v_a_793_ = stack[5].m_obj;
lean_object* v_a_794_ = stack[6].m_obj;
lean_object* v_res_816_;
v_res_816_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_788_, v_exceptionSet_789_, v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object* v_kind_817_, lean_object* v_exceptionSet_818_, lean_object* v_e_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
uint8_t v_kind_boxed_825_; lean_object* v_res_826_; 
v_kind_boxed_825_ = lean_unbox(v_kind_817_);
v_res_826_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_boxed_825_, v_exceptionSet_818_, v_e_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_826_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(lean_object* v_msgData_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_env_834_; uint8_t v___x_835_; lean_object* v_env_836_; lean_object* v___x_837_; lean_object* v_toCold_838_; lean_object* v_mctx_839_; lean_object* v_lctx_840_; lean_object* v_options_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_833_ = lean_st_ref_get(v___y_831_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_env_834_);
lean_dec(v___x_833_);
v___x_835_ = 0;
v_env_836_ = l_Lean_Environment_setRecordingDeps(v_env_834_, v___x_835_);
v___x_837_ = lean_st_ref_get(v___y_829_);
v_toCold_838_ = lean_ctor_get(v___y_830_, 0);
v_mctx_839_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_mctx_839_);
lean_dec(v___x_837_);
v_lctx_840_ = lean_ctor_get(v___y_828_, 2);
v_options_841_ = lean_ctor_get(v_toCold_838_, 2);
lean_inc_ref(v_options_841_);
lean_inc_ref(v_lctx_840_);
v___x_842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_842_, 0, v_env_836_);
lean_ctor_set(v___x_842_, 1, v_mctx_839_);
lean_ctor_set(v___x_842_, 2, v_lctx_840_);
lean_ctor_set(v___x_842_, 3, v_options_841_);
v___x_843_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_msgData_827_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_827_ = stack[0].m_obj;
lean_object* v___y_828_ = stack[1].m_obj;
lean_object* v___y_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v___y_831_ = stack[4].m_obj;
lean_object* v_res_845_;
v_res_845_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_852_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_853_; double v___x_854_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_float_of_nat(v___x_853_);
return v___x_854_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(lean_object* v_cls_858_, lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_ref_865_; lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_912_; 
v_ref_865_ = lean_ctor_get(v___y_862_, 2);
v___x_866_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_912_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_912_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_912_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v_traceState_872_; lean_object* v_env_873_; lean_object* v_nextMacroScope_874_; lean_object* v_ngen_875_; lean_object* v_auxDeclNGen_876_; lean_object* v_cache_877_; lean_object* v_recordedDeps_878_; lean_object* v_messages_879_; lean_object* v_infoState_880_; lean_object* v_snapshotTasks_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_911_; 
v___x_871_ = lean_st_ref_take(v___y_863_);
v_traceState_872_ = lean_ctor_get(v___x_871_, 4);
v_env_873_ = lean_ctor_get(v___x_871_, 0);
v_nextMacroScope_874_ = lean_ctor_get(v___x_871_, 1);
v_ngen_875_ = lean_ctor_get(v___x_871_, 2);
v_auxDeclNGen_876_ = lean_ctor_get(v___x_871_, 3);
v_cache_877_ = lean_ctor_get(v___x_871_, 5);
v_recordedDeps_878_ = lean_ctor_get(v___x_871_, 6);
v_messages_879_ = lean_ctor_get(v___x_871_, 7);
v_infoState_880_ = lean_ctor_get(v___x_871_, 8);
v_snapshotTasks_881_ = lean_ctor_get(v___x_871_, 9);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_911_ == 0)
{
v___x_883_ = v___x_871_;
v_isShared_884_ = v_isSharedCheck_911_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snapshotTasks_881_);
lean_inc(v_infoState_880_);
lean_inc(v_messages_879_);
lean_inc(v_recordedDeps_878_);
lean_inc(v_cache_877_);
lean_inc(v_traceState_872_);
lean_inc(v_auxDeclNGen_876_);
lean_inc(v_ngen_875_);
lean_inc(v_nextMacroScope_874_);
lean_inc(v_env_873_);
lean_dec(v___x_871_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_911_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint64_t v_tid_885_; lean_object* v_traces_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_910_; 
v_tid_885_ = lean_ctor_get_uint64(v_traceState_872_, sizeof(void*)*1);
v_traces_886_ = lean_ctor_get(v_traceState_872_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_traceState_872_);
if (v_isSharedCheck_910_ == 0)
{
v___x_888_ = v_traceState_872_;
v_isShared_889_ = v_isSharedCheck_910_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_traces_886_);
lean_dec(v_traceState_872_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_910_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; double v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_box(0);
v___x_892_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_893_ = 0;
v___x_894_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_895_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_895_, 0, v_cls_858_);
lean_ctor_set(v___x_895_, 1, v___x_891_);
lean_ctor_set(v___x_895_, 2, v___x_894_);
lean_ctor_set_float(v___x_895_, sizeof(void*)*3, v___x_892_);
lean_ctor_set_float(v___x_895_, sizeof(void*)*3 + 8, v___x_892_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*3 + 16, v___x_893_);
v___x_896_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_897_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v_a_867_);
lean_ctor_set(v___x_897_, 2, v___x_896_);
lean_inc(v_ref_865_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_ref_865_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_PersistentArray_push___redArg(v_traces_886_, v___x_898_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_899_);
v___x_901_ = v___x_888_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_899_);
lean_ctor_set_uint64(v_reuseFailAlloc_909_, sizeof(void*)*1, v_tid_885_);
v___x_901_ = v_reuseFailAlloc_909_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v___x_901_);
v___x_903_ = v___x_883_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_env_873_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_nextMacroScope_874_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_ngen_875_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_auxDeclNGen_876_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_908_, 5, v_cache_877_);
lean_ctor_set(v_reuseFailAlloc_908_, 6, v_recordedDeps_878_);
lean_ctor_set(v_reuseFailAlloc_908_, 7, v_messages_879_);
lean_ctor_set(v_reuseFailAlloc_908_, 8, v_infoState_880_);
lean_ctor_set(v_reuseFailAlloc_908_, 9, v_snapshotTasks_881_);
v___x_903_ = v_reuseFailAlloc_908_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_st_ref_put(v___y_863_, v___x_903_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_890_);
v___x_906_ = v___x_869_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_890_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_858_ = stack[0].m_obj;
lean_object* v_msg_859_ = stack[1].m_obj;
lean_object* v___y_860_ = stack[2].m_obj;
lean_object* v___y_861_ = stack[3].m_obj;
lean_object* v___y_862_ = stack[4].m_obj;
lean_object* v___y_863_ = stack[5].m_obj;
lean_object* v_res_913_;
v_res_913_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_858_, v_msg_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(lean_object* v_cls_914_, lean_object* v_msg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_914_, v_msg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_932_ = l_Lean_Name_append(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(uint8_t v_kind_936_, lean_object* v_exceptionSet_937_, lean_object* v_e_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_944_, 0, v_exceptionSet_937_);
lean_ctor_set_uint8(v___x_944_, sizeof(void*)*1, v_kind_936_);
v___x_945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
v___x_946_ = l_Lean_Meta_FindSplitImpl_visit(v_e_938_, v___x_944_, v___x_945_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec_ref_known(v___x_944_, 1);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_994_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_994_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_994_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_994_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_fst_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_992_; 
v_fst_951_ = lean_ctor_get(v_a_947_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v_a_947_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_a_947_, 1);
lean_dec(v_unused_993_);
v___x_953_ = v_a_947_;
v_isShared_954_ = v_isSharedCheck_992_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_fst_951_);
lean_dec(v_a_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_992_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
if (lean_obj_tag(v_fst_951_) == 1)
{
lean_object* v_toCold_955_; lean_object* v_options_956_; lean_object* v_val_957_; lean_object* v_inheritedTraceOptions_958_; uint8_t v_hasTrace_959_; lean_object* v___x_961_; 
v_toCold_955_ = lean_ctor_get(v_a_941_, 0);
v_options_956_ = lean_ctor_get(v_toCold_955_, 2);
v_val_957_ = lean_ctor_get(v_fst_951_, 0);
v_inheritedTraceOptions_958_ = lean_ctor_get(v_toCold_955_, 11);
v_hasTrace_959_ = lean_ctor_get_uint8(v_options_956_, sizeof(void*)*1);
lean_inc_ref(v_fst_951_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v_fst_951_);
v___x_961_ = v___x_949_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_fst_951_);
v___x_961_ = v_reuseFailAlloc_987_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
if (v_hasTrace_959_ == 0)
{
lean_dec_ref_known(v_fst_951_, 1);
lean_del_object(v___x_953_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2));
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
v___x_964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_958_, v_options_956_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref_known(v_fst_951_, 1);
lean_del_object(v___x_953_);
return v___x_961_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec_ref(v___x_961_);
v___x_965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
lean_inc(v_val_957_);
v___x_966_ = l_Lean_indentExpr(v_val_957_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 7);
lean_ctor_set(v___x_953_, 1, v___x_966_);
lean_ctor_set(v___x_953_, 0, v___x_965_);
v___x_968_ = v___x_953_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_986_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_962_, v___x_968_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_977_);
v___x_971_ = v___x_969_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_dec(v___x_969_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_fst_951_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_fst_951_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref_known(v_fst_951_, 1);
v_a_978_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_969_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_969_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
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
lean_object* v___x_988_; lean_object* v___x_990_; 
lean_del_object(v___x_953_);
lean_dec(v_fst_951_);
v___x_988_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_988_);
v___x_990_ = v___x_949_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
v_a_995_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_946_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_946_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_936_ = stack[0].m_num;
lean_object* v_exceptionSet_937_ = stack[1].m_obj;
lean_object* v_e_938_ = stack[2].m_obj;
lean_object* v_a_939_ = stack[3].m_obj;
lean_object* v_a_940_ = stack[4].m_obj;
lean_object* v_a_941_ = stack[5].m_obj;
lean_object* v_a_942_ = stack[6].m_obj;
lean_object* v_res_1003_;
v_res_1003_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_936_, v_exceptionSet_937_, v_e_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* v_kind_1004_, lean_object* v_exceptionSet_1005_, lean_object* v_e_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_kind_boxed_1012_; lean_object* v_res_1013_; 
v_kind_boxed_1012_ = lean_unbox(v_kind_1004_);
v_res_1013_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_boxed_1012_, v_exceptionSet_1005_, v_e_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1013_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(uint8_t v_kind_1014_, lean_object* v_exceptionSet_1015_, lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___y_1023_; lean_object* v___x_1026_; 
lean_inc_ref(v_exceptionSet_1015_);
v___x_1026_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(v_kind_1014_, v_exceptionSet_1015_, v_e_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
if (lean_obj_tag(v_a_1027_) == 1)
{
lean_object* v_val_1028_; uint8_t v___y_1030_; uint8_t v___x_1036_; 
v_val_1028_ = lean_ctor_get(v_a_1027_, 0);
v___x_1036_ = l_Lean_Expr_isIte(v_val_1028_);
if (v___x_1036_ == 0)
{
uint8_t v___x_1037_; 
v___x_1037_ = l_Lean_Expr_isDIte(v_val_1028_);
v___y_1030_ = v___x_1037_;
goto v___jp_1029_;
}
else
{
v___y_1030_ = v___x_1036_;
goto v___jp_1029_;
}
v___jp_1029_:
{
if (v___y_1030_ == 0)
{
lean_dec_ref(v_exceptionSet_1015_);
return v___x_1026_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_inc(v_val_1028_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1031_ = lean_unsigned_to_nat(3u);
v___x_1032_ = l_Lean_Expr_getRevArg_x21(v_val_1028_, v___x_1031_);
v___x_1033_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1014_, v_exceptionSet_1015_, v___x_1032_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
if (lean_obj_tag(v_a_1034_) == 0)
{
v___y_1023_ = v_val_1028_;
goto v___jp_1022_;
}
else
{
lean_object* v_val_1035_; 
lean_dec(v_val_1028_);
v_val_1035_ = lean_ctor_get(v_a_1034_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_a_1034_, 1);
v___y_1023_ = v_val_1035_;
goto v___jp_1022_;
}
}
else
{
lean_dec(v_val_1028_);
return v___x_1033_;
}
}
}
}
else
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_exceptionSet_1015_);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v___x_1026_, 0);
lean_dec(v_unused_1046_);
v___x_1039_ = v___x_1026_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v___x_1026_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = lean_box(0);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_dec_ref(v_exceptionSet_1015_);
return v___x_1026_;
}
v___jp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___y_1023_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_1014_ = stack[0].m_num;
lean_object* v_exceptionSet_1015_ = stack[1].m_obj;
lean_object* v_e_1016_ = stack[2].m_obj;
lean_object* v_a_1017_ = stack[3].m_obj;
lean_object* v_a_1018_ = stack[4].m_obj;
lean_object* v_a_1019_ = stack[5].m_obj;
lean_object* v_a_1020_ = stack[6].m_obj;
lean_object* v_res_1047_;
v_res_1047_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1014_, v_exceptionSet_1015_, v_e_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(lean_object* v_kind_1048_, lean_object* v_exceptionSet_1049_, lean_object* v_e_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
uint8_t v_kind_boxed_1056_; lean_object* v_res_1057_; 
v_kind_boxed_1056_ = lean_unbox(v_kind_1048_);
v_res_1057_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_boxed_1056_, v_exceptionSet_1049_, v_e_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1057_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(lean_object* v_e_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Lean_Expr_hasMVar(v_e_1058_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_e_1058_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v_mctx_1064_; lean_object* v___x_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1068_; lean_object* v_cache_1069_; lean_object* v_zetaDeltaFVarIds_1070_; lean_object* v_postponed_1071_; lean_object* v_diag_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1081_; 
v___x_1063_ = lean_st_ref_get(v___y_1059_);
v_mctx_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_mctx_1064_);
lean_dec(v___x_1063_);
v___x_1065_ = l_Lean_instantiateMVarsCore(v_mctx_1064_, v_e_1058_);
v_fst_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_snd_1067_);
lean_dec_ref(v___x_1065_);
v___x_1068_ = lean_st_ref_take(v___y_1059_);
v_cache_1069_ = lean_ctor_get(v___x_1068_, 1);
v_zetaDeltaFVarIds_1070_ = lean_ctor_get(v___x_1068_, 2);
v_postponed_1071_ = lean_ctor_get(v___x_1068_, 3);
v_diag_1072_ = lean_ctor_get(v___x_1068_, 4);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1082_);
v___x_1074_ = v___x_1068_;
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_diag_1072_);
lean_inc(v_postponed_1071_);
lean_inc(v_zetaDeltaFVarIds_1070_);
lean_inc(v_cache_1069_);
lean_dec(v___x_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_snd_1067_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_snd_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_cache_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_zetaDeltaFVarIds_1070_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_postponed_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_diag_1072_);
v___x_1077_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_st_ref_put(v___y_1059_, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_fst_1066_);
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1058_ = stack[0].m_obj;
lean_object* v___y_1059_ = stack[1].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1058_, v___y_1059_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(lean_object* v_e_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1084_, v___y_1085_);
lean_dec(v___y_1085_);
return v_res_1087_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(lean_object* v_e_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1088_, v___y_1090_);
return v___x_1094_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1088_ = stack[0].m_obj;
lean_object* v___y_1089_ = stack[1].m_obj;
lean_object* v___y_1090_ = stack[2].m_obj;
lean_object* v___y_1091_ = stack[3].m_obj;
lean_object* v___y_1092_ = stack[4].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(lean_object* v_e_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(v_e_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
lean_object* l_Lean_Meta_findSplit_x3f(lean_object* v_e_1103_, uint8_t v_kind_1104_, lean_object* v_exceptionSet_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_a_1112_; lean_object* v___x_1113_; 
v___x_1111_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_1103_, v_a_1107_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(v_kind_1104_, v_exceptionSet_1105_, v_a_1112_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
return v___x_1113_;
}
}
LEAN_EXPORT void l_Lean_Meta_findSplit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1103_ = stack[0].m_obj;
uint8_t v_kind_1104_ = stack[1].m_num;
lean_object* v_exceptionSet_1105_ = stack[2].m_obj;
lean_object* v_a_1106_ = stack[3].m_obj;
lean_object* v_a_1107_ = stack[4].m_obj;
lean_object* v_a_1108_ = stack[5].m_obj;
lean_object* v_a_1109_ = stack[6].m_obj;
lean_object* v_res_1114_;
v_res_1114_ = l_Lean_Meta_findSplit_x3f(v_e_1103_, v_kind_1104_, v_exceptionSet_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
stack->m_obj
 = v_res_1114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* v_e_1115_, lean_object* v_kind_1116_, lean_object* v_exceptionSet_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
uint8_t v_kind_boxed_1123_; lean_object* v_res_1124_; 
v_kind_boxed_1123_ = lean_unbox(v_kind_1116_);
v_res_1124_ = l_Lean_Meta_findSplit_x3f(v_e_1115_, v_kind_boxed_1123_, v_exceptionSet_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
return v_res_1124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_unsigned_to_nat(16u);
v___x_1127_ = lean_mk_array(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v___x_1128_);
return v___x_1130_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* v_e_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = 0;
v___x_1138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
v___x_1139_ = l_Lean_Meta_findSplit_x3f(v_e_1131_, v___x_1137_, v___x_1138_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1164_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
if (lean_obj_tag(v_a_1140_) == 1)
{
lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1159_; 
v_val_1144_ = lean_ctor_get(v_a_1140_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_a_1140_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1146_ = v_a_1140_;
v_isShared_1147_ = v_isSharedCheck_1159_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_dec(v_a_1140_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1159_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1148_ = lean_unsigned_to_nat(3u);
v___x_1149_ = l_Lean_Expr_getRevArg_x21(v_val_1144_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(2u);
v___x_1151_ = l_Lean_Expr_getRevArg_x21(v_val_1144_, v___x_1150_);
lean_dec(v_val_1144_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1149_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1152_);
v___x_1154_ = v___x_1146_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1154_);
v___x_1156_ = v___x_1142_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec(v_a_1140_);
v___x_1160_ = lean_box(0);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1160_);
v___x_1162_ = v___x_1142_;
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
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1139_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1139_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1131_ = stack[0].m_obj;
lean_object* v_a_1132_ = stack[1].m_obj;
lean_object* v_a_1133_ = stack[2].m_obj;
lean_object* v_a_1134_ = stack[3].m_obj;
lean_object* v_a_1135_ = stack[4].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(lean_object* v_e_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_e_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
return v_res_1180_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(lean_object* v_name_1181_, lean_object* v_decl_1182_, lean_object* v_ref_1183_){
_start:
{
lean_object* v_defValue_1185_; lean_object* v_descr_1186_; lean_object* v_deprecation_x3f_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_defValue_1185_ = lean_ctor_get(v_decl_1182_, 0);
v_descr_1186_ = lean_ctor_get(v_decl_1182_, 1);
v_deprecation_x3f_1187_ = lean_ctor_get(v_decl_1182_, 2);
v___x_1188_ = lean_alloc_ctor(1, 0, 1);
v___x_1189_ = lean_unbox(v_defValue_1185_);
lean_ctor_set_uint8(v___x_1188_, 0, v___x_1189_);
lean_inc(v_deprecation_x3f_1187_);
lean_inc_ref(v_descr_1186_);
lean_inc_n(v_name_1181_, 2);
v___x_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1190_, 0, v_name_1181_);
lean_ctor_set(v___x_1190_, 1, v_ref_1183_);
lean_ctor_set(v___x_1190_, 2, v___x_1188_);
lean_ctor_set(v___x_1190_, 3, v_descr_1186_);
lean_ctor_set(v___x_1190_, 4, v_deprecation_x3f_1187_);
v___x_1191_ = lean_register_option(v_name_1181_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v___x_1191_, 0);
lean_dec(v_unused_1200_);
v___x_1193_ = v___x_1191_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v___x_1191_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
lean_inc(v_defValue_1185_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_name_1181_);
lean_ctor_set(v___x_1195_, 1, v_defValue_1185_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_name_1181_);
v_a_1201_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1191_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1181_ = stack[0].m_obj;
lean_object* v_decl_1182_ = stack[1].m_obj;
lean_object* v_ref_1183_ = stack[2].m_obj;
lean_object* v_res_1209_;
v_res_1209_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1181_, v_decl_1182_, v_ref_1183_);
stack->m_obj
 = v_res_1209_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1210_, lean_object* v_decl_1211_, lean_object* v_ref_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_1210_, v_decl_1211_, v_ref_1212_);
lean_dec_ref(v_decl_1211_);
return v_res_1214_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_));
v___x_1236_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_1233_, v___x_1234_, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1237_;
v_res_1237_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
return v_res_1239_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg(){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__1);
return v___x_1244_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1245_;
v_res_1245_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg();
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___boxed(lean_object* v___dummy_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg();
return v_res_1247_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg();
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(lean_object* v_00_u03b2_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg(){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___closed__0);
return v___x_1254_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1255_;
v_res_1255_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg();
stack->m_obj
 = v_res_1255_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg___boxed(lean_object* v___dummy_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg();
return v_res_1257_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___redArg();
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(lean_object* v_00_u03b2_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0(void){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_s_1268_; 
v___x_1264_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__1, &l_Lean_Meta_SplitIf_getSimpContext___closed__1_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1);
v___x_1265_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_1266_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
v___x_1267_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_1268_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_1268_, 0, v___x_1267_);
lean_ctor_set(v_s_1268_, 1, v___x_1267_);
lean_ctor_set(v_s_1268_, 2, v___x_1266_);
lean_ctor_set(v_s_1268_, 3, v___x_1265_);
lean_ctor_set(v_s_1268_, 4, v___x_1266_);
lean_ctor_set(v_s_1268_, 5, v___x_1264_);
return v_s_1268_;
}
}
lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_s_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_s_1286_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__2, &l_Lean_Meta_SplitIf_getSimpContext___closed__2_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2);
v___x_1287_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__4));
v___x_1288_ = 1;
v___x_1289_ = 0;
v___x_1290_ = lean_unsigned_to_nat(1000u);
v___x_1291_ = l_Lean_Meta_SimpTheorems_addConst(v_s_1286_, v___x_1287_, v___x_1288_, v___x_1289_, v___x_1290_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__6));
v___x_1294_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1292_, v___x_1293_, v___x_1288_, v___x_1289_, v___x_1290_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__8));
v___x_1297_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1295_, v___x_1296_, v___x_1288_, v___x_1289_, v___x_1290_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__10));
v___x_1300_ = l_Lean_Meta_SimpTheorems_addConst(v_a_1298_, v___x_1299_, v___x_1288_, v___x_1289_, v___x_1290_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1284_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v_maxSteps_1305_; lean_object* v_maxDischargeDepth_1306_; uint8_t v_contextual_1307_; uint8_t v_memoize_1308_; uint8_t v_singlePass_1309_; uint8_t v_zeta_1310_; uint8_t v_beta_1311_; uint8_t v_eta_1312_; uint8_t v_etaStruct_1313_; uint8_t v_iota_1314_; uint8_t v_proj_1315_; uint8_t v_decide_1316_; uint8_t v_arith_1317_; uint8_t v_autoUnfold_1318_; uint8_t v_failIfUnchanged_1319_; uint8_t v_ground_1320_; uint8_t v_unfoldPartialApp_1321_; uint8_t v_zetaDelta_1322_; uint8_t v_index_1323_; uint8_t v_implicitDefEqProofs_1324_; uint8_t v_zetaUnused_1325_; uint8_t v_catchRuntime_1326_; uint8_t v_zetaHave_1327_; uint8_t v_congrConsts_1328_; uint8_t v_bitVecOfNat_1329_; uint8_t v_warnExponents_1330_; uint8_t v_suggestions_1331_; lean_object* v_maxSuggestions_1332_; uint8_t v_locals_1333_; uint8_t v_instances_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1305_ = lean_ctor_get(v___x_1304_, 0);
v_maxDischargeDepth_1306_ = lean_ctor_get(v___x_1304_, 1);
v_contextual_1307_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3);
v_memoize_1308_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 1);
v_singlePass_1309_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 2);
v_zeta_1310_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 3);
v_beta_1311_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 4);
v_eta_1312_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 5);
v_etaStruct_1313_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 6);
v_iota_1314_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 7);
v_proj_1315_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 8);
v_decide_1316_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 9);
v_arith_1317_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 10);
v_autoUnfold_1318_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1319_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 13);
v_ground_1320_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1321_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 15);
v_zetaDelta_1322_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 16);
v_index_1323_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1324_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 18);
v_zetaUnused_1325_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 19);
v_catchRuntime_1326_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 20);
v_zetaHave_1327_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 21);
v_congrConsts_1328_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1329_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 24);
v_warnExponents_1330_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 25);
v_suggestions_1331_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 26);
v_maxSuggestions_1332_ = lean_ctor_get(v___x_1304_, 2);
v_locals_1333_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 27);
v_instances_1334_ = lean_ctor_get_uint8(v___x_1304_, sizeof(void*)*3 + 28);
lean_inc(v_maxSuggestions_1332_);
lean_inc(v_maxDischargeDepth_1306_);
lean_inc(v_maxSteps_1305_);
v___x_1335_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1335_, 0, v_maxSteps_1305_);
lean_ctor_set(v___x_1335_, 1, v_maxDischargeDepth_1306_);
lean_ctor_set(v___x_1335_, 2, v_maxSuggestions_1332_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3, v_contextual_1307_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 1, v_memoize_1308_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 2, v_singlePass_1309_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 3, v_zeta_1310_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 4, v_beta_1311_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 5, v_eta_1312_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 6, v_etaStruct_1313_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 7, v_iota_1314_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 8, v_proj_1315_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 9, v_decide_1316_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 10, v_arith_1317_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 11, v_autoUnfold_1318_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 12, v___x_1289_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 13, v_failIfUnchanged_1319_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 14, v_ground_1320_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1321_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 16, v_zetaDelta_1322_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 17, v_index_1323_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1324_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 19, v_zetaUnused_1325_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 20, v_catchRuntime_1326_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 21, v_zetaHave_1327_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 22, v___x_1288_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 23, v_congrConsts_1328_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 24, v_bitVecOfNat_1329_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 25, v_warnExponents_1330_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 26, v_suggestions_1331_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 27, v_locals_1333_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 28, v_instances_1334_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_array_push(v___x_1337_, v_a_1301_);
v___x_1339_ = l_Lean_Options_empty;
v___x_1340_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1335_, v___x_1338_, v_a_1303_, v___x_1339_, v_a_1281_, v_a_1283_, v_a_1284_);
return v___x_1340_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_a_1301_);
v_a_1341_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1302_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1302_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1300_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1300_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1297_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1297_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1294_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1294_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1291_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1291_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SplitIf_getSimpContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1281_ = stack[0].m_obj;
lean_object* v_a_1282_ = stack[1].m_obj;
lean_object* v_a_1283_ = stack[2].m_obj;
lean_object* v_a_1284_ = stack[3].m_obj;
lean_object* v_res_1381_;
v_res_1381_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
stack->m_obj
 = v_res_1381_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1387_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1392_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; lean_object* v_maxSteps_1397_; lean_object* v_maxDischargeDepth_1398_; uint8_t v_contextual_1399_; uint8_t v_memoize_1400_; uint8_t v_singlePass_1401_; uint8_t v_zeta_1402_; uint8_t v_beta_1403_; uint8_t v_eta_1404_; uint8_t v_etaStruct_1405_; uint8_t v_iota_1406_; uint8_t v_proj_1407_; uint8_t v_decide_1408_; uint8_t v_arith_1409_; uint8_t v_autoUnfold_1410_; uint8_t v_failIfUnchanged_1411_; uint8_t v_ground_1412_; uint8_t v_unfoldPartialApp_1413_; uint8_t v_zetaDelta_1414_; uint8_t v_index_1415_; uint8_t v_implicitDefEqProofs_1416_; uint8_t v_zetaUnused_1417_; uint8_t v_catchRuntime_1418_; uint8_t v_zetaHave_1419_; uint8_t v_congrConsts_1420_; uint8_t v_bitVecOfNat_1421_; uint8_t v_warnExponents_1422_; uint8_t v_suggestions_1423_; lean_object* v_maxSuggestions_1424_; uint8_t v_locals_1425_; uint8_t v_instances_1426_; uint8_t v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_1397_ = lean_ctor_get(v___x_1396_, 0);
v_maxDischargeDepth_1398_ = lean_ctor_get(v___x_1396_, 1);
v_contextual_1399_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3);
v_memoize_1400_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 1);
v_singlePass_1401_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 2);
v_zeta_1402_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 3);
v_beta_1403_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 4);
v_eta_1404_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 5);
v_etaStruct_1405_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 6);
v_iota_1406_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 7);
v_proj_1407_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 8);
v_decide_1408_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 9);
v_arith_1409_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 10);
v_autoUnfold_1410_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 11);
v_failIfUnchanged_1411_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 13);
v_ground_1412_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_1413_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 15);
v_zetaDelta_1414_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 16);
v_index_1415_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_1416_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 18);
v_zetaUnused_1417_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 19);
v_catchRuntime_1418_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 20);
v_zetaHave_1419_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 21);
v_congrConsts_1420_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 23);
v_bitVecOfNat_1421_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 24);
v_warnExponents_1422_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 25);
v_suggestions_1423_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 26);
v_maxSuggestions_1424_ = lean_ctor_get(v___x_1396_, 2);
v_locals_1425_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 27);
v_instances_1426_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 28);
v___x_1427_ = 0;
v___x_1428_ = 1;
lean_inc(v_maxSuggestions_1424_);
lean_inc(v_maxDischargeDepth_1398_);
lean_inc(v_maxSteps_1397_);
v___x_1429_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1429_, 0, v_maxSteps_1397_);
lean_ctor_set(v___x_1429_, 1, v_maxDischargeDepth_1398_);
lean_ctor_set(v___x_1429_, 2, v_maxSuggestions_1424_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3, v_contextual_1399_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 1, v_memoize_1400_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 2, v_singlePass_1401_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 3, v_zeta_1402_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 4, v_beta_1403_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 5, v_eta_1404_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 6, v_etaStruct_1405_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 7, v_iota_1406_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 8, v_proj_1407_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 9, v_decide_1408_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 10, v_arith_1409_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 11, v_autoUnfold_1410_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 12, v___x_1427_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 13, v_failIfUnchanged_1411_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 14, v_ground_1412_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 15, v_unfoldPartialApp_1413_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 16, v_zetaDelta_1414_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 17, v_index_1415_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_1416_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 19, v_zetaUnused_1417_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 20, v_catchRuntime_1418_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 21, v_zetaHave_1419_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 22, v___x_1428_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 23, v_congrConsts_1420_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 24, v_bitVecOfNat_1421_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 25, v_warnExponents_1422_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 26, v_suggestions_1423_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 27, v_locals_1425_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*3 + 28, v_instances_1426_);
v___x_1430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0));
v___x_1431_ = l_Lean_Options_empty;
v___x_1432_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1429_, v___x_1430_, v_a_1395_, v___x_1431_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1432_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1394_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1394_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1390_ = stack[0].m_obj;
lean_object* v_a_1391_ = stack[1].m_obj;
lean_object* v_a_1392_ = stack[2].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1390_, v_a_1391_, v_a_1392_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1446_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_1447_, v_a_1449_, v_a_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1447_ = stack[0].m_obj;
lean_object* v_a_1448_ = stack[1].m_obj;
lean_object* v_a_1449_ = stack[2].m_obj;
lean_object* v_a_1450_ = stack[3].m_obj;
lean_object* v_res_1453_;
v_res_1453_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
return v_res_1459_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(lean_object* v_e_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v___x_1463_; 
v___x_1463_ = l_Lean_Expr_hasMVar(v_e_1460_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_e_1460_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; lean_object* v_mctx_1466_; lean_object* v___x_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v___x_1470_; lean_object* v_cache_1471_; lean_object* v_zetaDeltaFVarIds_1472_; lean_object* v_postponed_1473_; lean_object* v_diag_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1483_; 
v___x_1465_ = lean_st_ref_get(v___y_1461_);
v_mctx_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc_ref(v_mctx_1466_);
lean_dec(v___x_1465_);
v___x_1467_ = l_Lean_instantiateMVarsCore(v_mctx_1466_, v_e_1460_);
v_fst_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_fst_1468_);
v_snd_1469_ = lean_ctor_get(v___x_1467_, 1);
lean_inc(v_snd_1469_);
lean_dec_ref(v___x_1467_);
v___x_1470_ = lean_st_ref_take(v___y_1461_);
v_cache_1471_ = lean_ctor_get(v___x_1470_, 1);
v_zetaDeltaFVarIds_1472_ = lean_ctor_get(v___x_1470_, 2);
v_postponed_1473_ = lean_ctor_get(v___x_1470_, 3);
v_diag_1474_ = lean_ctor_get(v___x_1470_, 4);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1484_);
v___x_1476_ = v___x_1470_;
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_diag_1474_);
lean_inc(v_postponed_1473_);
lean_inc(v_zetaDeltaFVarIds_1472_);
lean_inc(v_cache_1471_);
lean_dec(v___x_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v_snd_1469_);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_snd_1469_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_cache_1471_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_zetaDeltaFVarIds_1472_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_postponed_1473_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_diag_1474_);
v___x_1479_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_st_ref_put(v___y_1461_, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_fst_1468_);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1460_ = stack[0].m_obj;
lean_object* v___y_1461_ = stack[1].m_obj;
lean_object* v_res_1485_;
v_res_1485_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1460_, v___y_1461_);
stack->m_obj
 = v_res_1485_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(lean_object* v_e_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1486_, v___y_1487_);
lean_dec(v___y_1487_);
return v_res_1489_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* v_e_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_1490_, v___y_1495_);
return v___x_1499_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1490_ = stack[0].m_obj;
lean_object* v___y_1491_ = stack[1].m_obj;
lean_object* v___y_1492_ = stack[2].m_obj;
lean_object* v___y_1493_ = stack[3].m_obj;
lean_object* v___y_1494_ = stack[4].m_obj;
lean_object* v___y_1495_ = stack[5].m_obj;
lean_object* v___y_1496_ = stack[6].m_obj;
lean_object* v___y_1497_ = stack[7].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* v_e_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
return v_res_1510_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(lean_object* v_cls_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_ref_1518_; lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1565_; 
v_ref_1518_ = lean_ctor_get(v___y_1515_, 2);
v___x_1519_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1565_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1565_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v_traceState_1525_; lean_object* v_env_1526_; lean_object* v_nextMacroScope_1527_; lean_object* v_ngen_1528_; lean_object* v_auxDeclNGen_1529_; lean_object* v_cache_1530_; lean_object* v_recordedDeps_1531_; lean_object* v_messages_1532_; lean_object* v_infoState_1533_; lean_object* v_snapshotTasks_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1564_; 
v___x_1524_ = lean_st_ref_take(v___y_1516_);
v_traceState_1525_ = lean_ctor_get(v___x_1524_, 4);
v_env_1526_ = lean_ctor_get(v___x_1524_, 0);
v_nextMacroScope_1527_ = lean_ctor_get(v___x_1524_, 1);
v_ngen_1528_ = lean_ctor_get(v___x_1524_, 2);
v_auxDeclNGen_1529_ = lean_ctor_get(v___x_1524_, 3);
v_cache_1530_ = lean_ctor_get(v___x_1524_, 5);
v_recordedDeps_1531_ = lean_ctor_get(v___x_1524_, 6);
v_messages_1532_ = lean_ctor_get(v___x_1524_, 7);
v_infoState_1533_ = lean_ctor_get(v___x_1524_, 8);
v_snapshotTasks_1534_ = lean_ctor_get(v___x_1524_, 9);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1536_ = v___x_1524_;
v_isShared_1537_ = v_isSharedCheck_1564_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_snapshotTasks_1534_);
lean_inc(v_infoState_1533_);
lean_inc(v_messages_1532_);
lean_inc(v_recordedDeps_1531_);
lean_inc(v_cache_1530_);
lean_inc(v_traceState_1525_);
lean_inc(v_auxDeclNGen_1529_);
lean_inc(v_ngen_1528_);
lean_inc(v_nextMacroScope_1527_);
lean_inc(v_env_1526_);
lean_dec(v___x_1524_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1564_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint64_t v_tid_1538_; lean_object* v_traces_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1563_; 
v_tid_1538_ = lean_ctor_get_uint64(v_traceState_1525_, sizeof(void*)*1);
v_traces_1539_ = lean_ctor_get(v_traceState_1525_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_traceState_1525_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1541_ = v_traceState_1525_;
v_isShared_1542_ = v_isSharedCheck_1563_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_traces_1539_);
lean_dec(v_traceState_1525_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1563_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; double v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
v___x_1546_ = 0;
v___x_1547_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1));
v___x_1548_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1548_, 0, v_cls_1511_);
lean_ctor_set(v___x_1548_, 1, v___x_1544_);
lean_ctor_set(v___x_1548_, 2, v___x_1547_);
lean_ctor_set_float(v___x_1548_, sizeof(void*)*3, v___x_1545_);
lean_ctor_set_float(v___x_1548_, sizeof(void*)*3 + 8, v___x_1545_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*3 + 16, v___x_1546_);
v___x_1549_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2));
v___x_1550_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v_a_1520_);
lean_ctor_set(v___x_1550_, 2, v___x_1549_);
lean_inc(v_ref_1518_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_ref_1518_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_PersistentArray_push___redArg(v_traces_1539_, v___x_1551_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1552_);
v___x_1554_ = v___x_1541_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1552_);
lean_ctor_set_uint64(v_reuseFailAlloc_1562_, sizeof(void*)*1, v_tid_1538_);
v___x_1554_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 4, v___x_1554_);
v___x_1556_ = v___x_1536_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_env_1526_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_nextMacroScope_1527_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_ngen_1528_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_auxDeclNGen_1529_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1561_, 5, v_cache_1530_);
lean_ctor_set(v_reuseFailAlloc_1561_, 6, v_recordedDeps_1531_);
lean_ctor_set(v_reuseFailAlloc_1561_, 7, v_messages_1532_);
lean_ctor_set(v_reuseFailAlloc_1561_, 8, v_infoState_1533_);
lean_ctor_set(v_reuseFailAlloc_1561_, 9, v_snapshotTasks_1534_);
v___x_1556_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_st_ref_put(v___y_1516_, v___x_1556_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1543_);
v___x_1559_ = v___x_1522_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1543_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1511_ = stack[0].m_obj;
lean_object* v_msg_1512_ = stack[1].m_obj;
lean_object* v___y_1513_ = stack[2].m_obj;
lean_object* v___y_1514_ = stack[3].m_obj;
lean_object* v___y_1515_ = stack[4].m_obj;
lean_object* v___y_1516_ = stack[5].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1511_, v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
stack->m_obj
 = v_res_1566_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(lean_object* v_cls_1567_, lean_object* v_msg_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1567_, v_msg_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3));
v___x_1583_ = l_Lean_mkConst(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_numIndices_1584_, lean_object* v_a_1585_, lean_object* v_as_1586_, lean_object* v_i_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_zero_1593_; uint8_t v_isZero_1594_; 
v_zero_1593_ = lean_unsigned_to_nat(0u);
v_isZero_1594_ = lean_nat_dec_eq(v_i_1587_, v_zero_1593_);
if (v_isZero_1594_ == 1)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_i_1587_);
lean_dec_ref(v_a_1585_);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
else
{
lean_object* v_one_1597_; lean_object* v_n_1598_; lean_object* v___x_1599_; 
v_one_1597_ = lean_unsigned_to_nat(1u);
v_n_1598_ = lean_nat_sub(v_i_1587_, v_one_1597_);
lean_dec(v_i_1587_);
v___x_1599_ = lean_array_fget(v_as_1586_, v_n_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
v_i_1587_ = v_n_1598_;
goto _start;
}
else
{
lean_object* v_val_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1665_; 
v_val_1601_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1603_ = v___x_1599_;
v_isShared_1604_ = v_isSharedCheck_1665_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_val_1601_);
lean_dec(v___x_1599_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1665_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = l_Lean_LocalDecl_index(v_val_1601_);
v___x_1606_ = lean_nat_dec_le(v_numIndices_1584_, v___x_1605_);
lean_dec(v___x_1605_);
if (v___x_1606_ == 0)
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_LocalDecl_isAuxDecl(v_val_1601_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = l_Lean_LocalDecl_type(v_val_1601_);
lean_inc_ref(v___x_1608_);
lean_inc_ref(v_a_1585_);
v___x_1609_ = l_Lean_Meta_isExprDefEq(v_a_1585_, v___x_1608_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1654_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1654_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1654_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_unbox(v_a_1610_);
lean_dec(v_a_1610_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
lean_del_object(v___x_1612_);
v___x_1615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1616_ = l_Lean_Expr_isAppOfArity(v_a_1585_, v___x_1615_, v_one_1597_);
if (v___x_1616_ == 0)
{
lean_dec_ref(v___x_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
v_i_1587_ = v_n_1598_;
goto _start;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = l_Lean_Expr_appArg_x21(v_a_1585_);
v___x_1619_ = l_Lean_Expr_isAppOfArity(v___x_1618_, v___x_1615_, v_one_1597_);
if (v___x_1619_ == 0)
{
lean_dec_ref(v___x_1618_);
lean_dec_ref(v___x_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
v_i_1587_ = v_n_1598_;
goto _start;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_Expr_appArg_x21(v___x_1618_);
lean_dec_ref(v___x_1618_);
lean_inc_ref(v___x_1621_);
v___x_1622_ = l_Lean_Meta_isExprDefEq(v___x_1621_, v___x_1608_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1638_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1638_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1638_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
uint8_t v___x_1627_; 
v___x_1627_ = lean_unbox(v_a_1623_);
lean_dec(v_a_1623_);
if (v___x_1627_ == 0)
{
lean_del_object(v___x_1625_);
lean_dec_ref(v___x_1621_);
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
v_i_1587_ = v_n_1598_;
goto _start;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_dec(v_n_1598_);
lean_dec_ref(v_a_1585_);
v___x_1629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_1630_ = l_Lean_LocalDecl_toExpr(v_val_1601_);
v___x_1631_ = l_Lean_mkAppB(v___x_1629_, v___x_1621_, v___x_1630_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1631_);
v___x_1633_ = v___x_1603_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1633_);
v___x_1635_ = v___x_1625_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___x_1621_);
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
lean_dec(v_n_1598_);
lean_dec_ref(v_a_1585_);
v_a_1639_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1622_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1622_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_dec_ref(v___x_1608_);
lean_dec(v_n_1598_);
lean_dec_ref(v_a_1585_);
v___x_1647_ = l_Lean_LocalDecl_toExpr(v_val_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1647_);
v___x_1649_ = v___x_1603_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1649_);
v___x_1651_ = v___x_1612_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
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
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v___x_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
lean_dec(v_n_1598_);
lean_dec_ref(v_a_1585_);
v_a_1655_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1609_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1609_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
v_i_1587_ = v_n_1598_;
goto _start;
}
}
else
{
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
v_i_1587_ = v_n_1598_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1584_ = stack[0].m_obj;
lean_object* v_a_1585_ = stack[1].m_obj;
lean_object* v_as_1586_ = stack[2].m_obj;
lean_object* v_i_1587_ = stack[3].m_obj;
lean_object* v___y_1588_ = stack[4].m_obj;
lean_object* v___y_1589_ = stack[5].m_obj;
lean_object* v___y_1590_ = stack[6].m_obj;
lean_object* v___y_1591_ = stack[7].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1584_, v_a_1585_, v_as_1586_, v_i_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_numIndices_1667_, lean_object* v_a_1668_, lean_object* v_as_1669_, lean_object* v_i_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1667_, v_a_1668_, v_as_1669_, v_i_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_as_1669_);
lean_dec(v_numIndices_1667_);
return v_res_1676_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_numIndices_1677_, lean_object* v_a_1678_, lean_object* v_as_1679_, lean_object* v_i_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_zero_1689_; uint8_t v_isZero_1690_; 
v_zero_1689_ = lean_unsigned_to_nat(0u);
v_isZero_1690_ = lean_nat_dec_eq(v_i_1680_, v_zero_1689_);
if (v_isZero_1690_ == 1)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_i_1680_);
lean_dec_ref(v_a_1678_);
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v_one_1693_; lean_object* v_n_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_one_1693_ = lean_unsigned_to_nat(1u);
v_n_1694_ = lean_nat_sub(v_i_1680_, v_one_1693_);
lean_dec(v_i_1680_);
v___x_1695_ = lean_array_fget_borrowed(v_as_1679_, v_n_1694_);
lean_inc_ref(v_a_1678_);
v___x_1696_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1677_, v_a_1678_, v___x_1695_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
if (lean_obj_tag(v_a_1697_) == 0)
{
lean_dec_ref_known(v___x_1696_, 1);
v_i_1680_ = v_n_1694_;
goto _start;
}
else
{
lean_dec(v_n_1694_);
lean_dec_ref(v_a_1678_);
return v___x_1696_;
}
}
else
{
lean_dec(v_n_1694_);
lean_dec_ref(v_a_1678_);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1677_ = stack[0].m_obj;
lean_object* v_a_1678_ = stack[1].m_obj;
lean_object* v_as_1679_ = stack[2].m_obj;
lean_object* v_i_1680_ = stack[3].m_obj;
lean_object* v___y_1681_ = stack[4].m_obj;
lean_object* v___y_1682_ = stack[5].m_obj;
lean_object* v___y_1683_ = stack[6].m_obj;
lean_object* v___y_1684_ = stack[7].m_obj;
lean_object* v___y_1685_ = stack[8].m_obj;
lean_object* v___y_1686_ = stack[9].m_obj;
lean_object* v___y_1687_ = stack[10].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1677_, v_a_1678_, v_as_1679_, v_i_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
stack->m_obj
 = v_res_1699_;
}
lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(lean_object* v_numIndices_1700_, lean_object* v_a_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_object* v_cs_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_cs_1711_ = lean_ctor_get(v_x_1702_, 0);
v___x_1712_ = lean_array_get_size(v_cs_1711_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1700_, v_a_1701_, v_cs_1711_, v___x_1712_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1713_;
}
else
{
lean_object* v_vs_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_vs_1714_ = lean_ctor_get(v_x_1702_, 0);
v___x_1715_ = lean_array_get_size(v_vs_1714_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1700_, v_a_1701_, v_vs_1714_, v___x_1715_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1716_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1700_ = stack[0].m_obj;
lean_object* v_a_1701_ = stack[1].m_obj;
lean_object* v_x_1702_ = stack[2].m_obj;
lean_object* v___y_1703_ = stack[3].m_obj;
lean_object* v___y_1704_ = stack[4].m_obj;
lean_object* v___y_1705_ = stack[5].m_obj;
lean_object* v___y_1706_ = stack[6].m_obj;
lean_object* v___y_1707_ = stack[7].m_obj;
lean_object* v___y_1708_ = stack[8].m_obj;
lean_object* v___y_1709_ = stack[9].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1700_, v_a_1701_, v_x_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_numIndices_1718_, lean_object* v_a_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1718_, v_a_1719_, v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v_x_1720_);
lean_dec(v_numIndices_1718_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_numIndices_1730_, lean_object* v_a_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_1730_, v_a_1731_, v_as_1732_, v_i_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v_as_1732_);
lean_dec(v_numIndices_1730_);
return v_res_1742_;
}
}
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(lean_object* v_numIndices_1743_, lean_object* v_a_1744_, lean_object* v_t_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_root_1754_; lean_object* v_tail_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_root_1754_ = lean_ctor_get(v_t_1745_, 0);
v_tail_1755_ = lean_ctor_get(v_t_1745_, 1);
v___x_1756_ = lean_array_get_size(v_tail_1755_);
lean_inc_ref(v_a_1744_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_1743_, v_a_1744_, v_tail_1755_, v___x_1756_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
if (lean_obj_tag(v_a_1758_) == 0)
{
lean_object* v___x_1759_; 
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_numIndices_1743_, v_a_1744_, v_root_1754_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1759_;
}
else
{
lean_dec_ref(v_a_1744_);
return v___x_1757_;
}
}
else
{
lean_dec_ref(v_a_1744_);
return v___x_1757_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1743_ = stack[0].m_obj;
lean_object* v_a_1744_ = stack[1].m_obj;
lean_object* v_t_1745_ = stack[2].m_obj;
lean_object* v___y_1746_ = stack[3].m_obj;
lean_object* v___y_1747_ = stack[4].m_obj;
lean_object* v___y_1748_ = stack[5].m_obj;
lean_object* v___y_1749_ = stack[6].m_obj;
lean_object* v___y_1750_ = stack[7].m_obj;
lean_object* v___y_1751_ = stack[8].m_obj;
lean_object* v___y_1752_ = stack[9].m_obj;
lean_object* v_res_1760_;
v_res_1760_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1743_, v_a_1744_, v_t_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
stack->m_obj
 = v_res_1760_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(lean_object* v_numIndices_1761_, lean_object* v_a_1762_, lean_object* v_t_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1761_, v_a_1762_, v_t_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v_t_1763_);
lean_dec(v_numIndices_1761_);
return v_res_1772_;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(lean_object* v_numIndices_1773_, lean_object* v_a_1774_, lean_object* v_lctx_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_decls_1784_; lean_object* v___x_1785_; 
v_decls_1784_ = lean_ctor_get(v_lctx_1775_, 1);
v___x_1785_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_numIndices_1773_, v_a_1774_, v_decls_1784_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1785_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1773_ = stack[0].m_obj;
lean_object* v_a_1774_ = stack[1].m_obj;
lean_object* v_lctx_1775_ = stack[2].m_obj;
lean_object* v___y_1776_ = stack[3].m_obj;
lean_object* v___y_1777_ = stack[4].m_obj;
lean_object* v___y_1778_ = stack[5].m_obj;
lean_object* v___y_1779_ = stack[6].m_obj;
lean_object* v___y_1780_ = stack[7].m_obj;
lean_object* v___y_1781_ = stack[8].m_obj;
lean_object* v___y_1782_ = stack[9].m_obj;
lean_object* v_res_1786_;
v_res_1786_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1773_, v_a_1774_, v_lctx_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
stack->m_obj
 = v_res_1786_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(lean_object* v_numIndices_1787_, lean_object* v_a_1788_, lean_object* v_lctx_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1787_, v_a_1788_, v_lctx_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v_lctx_1789_);
lean_dec(v_numIndices_1787_);
return v_res_1798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_box(0);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1806_ = l_Lean_mkConst(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5));
v___x_1812_ = l_Lean_mkConst(v___x_1811_, v___x_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_1821_ = l_Lean_Name_append(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11));
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13));
v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16));
v___x_1832_ = l_Lean_MessageData_ofFormat(v___x_1831_);
return v___x_1832_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* v_numIndices_1833_, uint8_t v_useDecide_1834_, lean_object* v_prop_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1979_; 
v___x_1844_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_1835_, v_a_1840_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1979_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1979_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v_toCold_1946_; lean_object* v_options_1947_; uint8_t v_hasTrace_1948_; 
v_toCold_1946_ = lean_ctor_get(v_a_1841_, 0);
v_options_1947_ = lean_ctor_get(v_toCold_1946_, 2);
v_hasTrace_1948_ = lean_ctor_get_uint8(v_options_1947_, sizeof(void*)*1);
if (v_hasTrace_1948_ == 0)
{
v___y_1906_ = v_a_1836_;
v___y_1907_ = v_a_1837_;
v___y_1908_ = v_a_1838_;
v___y_1909_ = v_a_1839_;
v___y_1910_ = v_a_1840_;
v___y_1911_ = v_a_1841_;
v___y_1912_ = v_a_1842_;
goto v___jp_1905_;
}
else
{
lean_object* v_inheritedTraceOptions_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_inheritedTraceOptions_1949_ = lean_ctor_get(v_toCold_1946_, 11);
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_1951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_1952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1949_, v_options_1947_, v___x_1951_);
if (v___x_1952_ == 0)
{
v___y_1906_ = v_a_1836_;
v___y_1907_ = v_a_1837_;
v___y_1908_ = v_a_1838_;
v___y_1909_ = v_a_1839_;
v___y_1910_ = v_a_1840_;
v___y_1911_ = v_a_1841_;
v___y_1912_ = v_a_1842_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___y_1959_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12);
lean_inc(v_a_1845_);
v___x_1954_ = l_Lean_MessageData_ofExpr(v_a_1845_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = l_Lean_Expr_isAppOfArity(v_a_1845_, v___x_1972_, v___x_1973_);
if (v___x_1974_ == 0)
{
goto v___jp_1970_;
}
else
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = l_Lean_Expr_appArg_x21(v_a_1845_);
v___x_1976_ = l_Lean_Expr_isAppOfArity(v___x_1975_, v___x_1972_, v___x_1973_);
if (v___x_1976_ == 0)
{
lean_dec_ref(v___x_1975_);
goto v___jp_1970_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = l_Lean_Expr_appArg_x21(v___x_1975_);
lean_dec_ref(v___x_1975_);
v___x_1978_ = l_Lean_MessageData_ofExpr(v___x_1977_);
v___y_1959_ = v___x_1978_;
goto v___jp_1958_;
}
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1957_);
lean_ctor_set(v___x_1960_, 1, v___y_1959_);
v___x_1961_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_1950_, v___x_1960_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
v___y_1906_ = v_a_1836_;
v___y_1907_ = v_a_1837_;
v___y_1908_ = v_a_1838_;
v___y_1909_ = v_a_1839_;
v___y_1910_ = v_a_1840_;
v___y_1911_ = v_a_1841_;
v___y_1912_ = v_a_1842_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_del_object(v___x_1847_);
lean_dec(v_a_1845_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
v___jp_1970_:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17);
v___y_1959_ = v___x_1971_;
goto v___jp_1958_;
}
}
}
v___jp_1849_:
{
lean_object* v_lctx_1857_; lean_object* v___x_1858_; 
v_lctx_1857_ = lean_ctor_get(v___y_1853_, 2);
v___x_1858_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_numIndices_1833_, v_a_1845_, v_lctx_1857_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
v___jp_1859_:
{
if (lean_obj_tag(v___y_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_a_1870_ = lean_ctor_get(v___y_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___y_1869_, 1);
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2));
v___x_1872_ = l_Lean_Expr_isConstOf(v_a_1870_, v___x_1871_);
lean_dec(v_a_1870_);
if (v___x_1872_ == 0)
{
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___y_1860_);
lean_del_object(v___x_1847_);
v___y_1850_ = v___y_1861_;
v___y_1851_ = v___y_1866_;
v___y_1852_ = v___y_1865_;
v___y_1853_ = v___y_1862_;
v___y_1854_ = v___y_1864_;
v___y_1855_ = v___y_1868_;
v___y_1856_ = v___y_1867_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v_a_1845_);
v___x_1873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
v___x_1874_ = l_Lean_Meta_mkEqRefl(v___x_1873_, v___y_1862_, v___y_1864_, v___y_1868_, v___y_1867_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1888_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
v___x_1880_ = l_Lean_Expr_appArg_x21(v___y_1863_);
lean_dec_ref(v___y_1863_);
v___x_1881_ = l_Lean_mkApp3(v___x_1879_, v___y_1860_, v___x_1880_, v_a_1875_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 1);
lean_ctor_set(v___x_1847_, 0, v___x_1881_);
v___x_1883_ = v___x_1847_;
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
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1883_);
v___x_1885_ = v___x_1877_;
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
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___y_1860_);
lean_del_object(v___x_1847_);
v_a_1889_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1874_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1874_);
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
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___y_1860_);
lean_del_object(v___x_1847_);
lean_dec(v_a_1845_);
v_a_1897_ = lean_ctor_get(v___y_1869_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___y_1869_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___y_1869_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___y_1869_);
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
v___jp_1905_:
{
if (v_useDecide_1834_ == 0)
{
lean_del_object(v___x_1847_);
v___y_1850_ = v___y_1906_;
v___y_1851_ = v___y_1907_;
v___y_1852_ = v___y_1908_;
v___y_1853_ = v___y_1909_;
v___y_1854_ = v___y_1910_;
v___y_1855_ = v___y_1911_;
v___y_1856_ = v___y_1912_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1913_; lean_object* v_a_1914_; uint8_t v___x_1915_; 
lean_inc(v_a_1845_);
v___x_1913_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_1845_, v___y_1910_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = l_Lean_Expr_hasFVar(v_a_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Expr_hasMVar(v_a_1914_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_inc(v_a_1914_);
v___x_1917_ = l_Lean_Meta_mkDecide(v_a_1914_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; uint8_t v_transparency_1920_; uint8_t v___x_1921_; uint8_t v___x_1922_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l_Lean_Meta_Context_config(v___y_1909_);
v_transparency_1920_ = lean_ctor_get_uint8(v___x_1919_, 9);
lean_dec_ref(v___x_1919_);
v___x_1921_ = 1;
v___x_1922_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v_keyedConfig_1923_; uint8_t v_trackZetaDelta_1924_; lean_object* v_zetaDeltaSet_1925_; lean_object* v_lctx_1926_; lean_object* v_localInstances_1927_; lean_object* v_defEqCtx_x3f_1928_; lean_object* v_synthPendingDepth_1929_; lean_object* v_customCanUnfoldPredicate_x3f_1930_; uint8_t v_univApprox_1931_; uint8_t v_inTypeClassResolution_1932_; uint8_t v_cacheInferType_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_keyedConfig_1923_ = lean_ctor_get(v___y_1909_, 0);
v_trackZetaDelta_1924_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*7);
v_zetaDeltaSet_1925_ = lean_ctor_get(v___y_1909_, 1);
v_lctx_1926_ = lean_ctor_get(v___y_1909_, 2);
v_localInstances_1927_ = lean_ctor_get(v___y_1909_, 3);
v_defEqCtx_x3f_1928_ = lean_ctor_get(v___y_1909_, 4);
v_synthPendingDepth_1929_ = lean_ctor_get(v___y_1909_, 5);
v_customCanUnfoldPredicate_x3f_1930_ = lean_ctor_get(v___y_1909_, 6);
v_univApprox_1931_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1932_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*7 + 2);
v_cacheInferType_1933_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1923_);
v___x_1934_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1921_, v_keyedConfig_1923_);
lean_inc(v_customCanUnfoldPredicate_x3f_1930_);
lean_inc(v_synthPendingDepth_1929_);
lean_inc(v_defEqCtx_x3f_1928_);
lean_inc_ref(v_localInstances_1927_);
lean_inc_ref(v_lctx_1926_);
lean_inc(v_zetaDeltaSet_1925_);
v___x_1935_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_zetaDeltaSet_1925_);
lean_ctor_set(v___x_1935_, 2, v_lctx_1926_);
lean_ctor_set(v___x_1935_, 3, v_localInstances_1927_);
lean_ctor_set(v___x_1935_, 4, v_defEqCtx_x3f_1928_);
lean_ctor_set(v___x_1935_, 5, v_synthPendingDepth_1929_);
lean_ctor_set(v___x_1935_, 6, v_customCanUnfoldPredicate_x3f_1930_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*7, v_trackZetaDelta_1924_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*7 + 1, v_univApprox_1931_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1932_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*7 + 3, v_cacheInferType_1933_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc(v_a_1918_);
v___x_1936_ = lean_whnf(v_a_1918_, v___x_1935_, v___y_1910_, v___y_1911_, v___y_1912_);
v___y_1860_ = v_a_1914_;
v___y_1861_ = v___y_1906_;
v___y_1862_ = v___y_1909_;
v___y_1863_ = v_a_1918_;
v___y_1864_ = v___y_1910_;
v___y_1865_ = v___y_1908_;
v___y_1866_ = v___y_1907_;
v___y_1867_ = v___y_1912_;
v___y_1868_ = v___y_1911_;
v___y_1869_ = v___x_1936_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1937_; 
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v_a_1918_);
v___x_1937_ = lean_whnf(v_a_1918_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
v___y_1860_ = v_a_1914_;
v___y_1861_ = v___y_1906_;
v___y_1862_ = v___y_1909_;
v___y_1863_ = v_a_1918_;
v___y_1864_ = v___y_1910_;
v___y_1865_ = v___y_1908_;
v___y_1866_ = v___y_1907_;
v___y_1867_ = v___y_1912_;
v___y_1868_ = v___y_1911_;
v___y_1869_ = v___x_1937_;
goto v___jp_1859_;
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1914_);
lean_del_object(v___x_1847_);
lean_dec(v_a_1845_);
v_a_1938_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1917_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1917_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_dec(v_a_1914_);
lean_del_object(v___x_1847_);
v___y_1850_ = v___y_1906_;
v___y_1851_ = v___y_1907_;
v___y_1852_ = v___y_1908_;
v___y_1853_ = v___y_1909_;
v___y_1854_ = v___y_1910_;
v___y_1855_ = v___y_1911_;
v___y_1856_ = v___y_1912_;
goto v___jp_1849_;
}
}
else
{
lean_dec(v_a_1914_);
lean_del_object(v___x_1847_);
v___y_1850_ = v___y_1906_;
v___y_1851_ = v___y_1907_;
v___y_1852_ = v___y_1908_;
v___y_1853_ = v___y_1909_;
v___y_1854_ = v___y_1910_;
v___y_1855_ = v___y_1911_;
v___y_1856_ = v___y_1912_;
goto v___jp_1849_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1833_ = stack[0].m_obj;
uint8_t v_useDecide_1834_ = stack[1].m_num;
lean_object* v_prop_1835_ = stack[2].m_obj;
lean_object* v_a_1836_ = stack[3].m_obj;
lean_object* v_a_1837_ = stack[4].m_obj;
lean_object* v_a_1838_ = stack[5].m_obj;
lean_object* v_a_1839_ = stack[6].m_obj;
lean_object* v_a_1840_ = stack[7].m_obj;
lean_object* v_a_1841_ = stack[8].m_obj;
lean_object* v_a_1842_ = stack[9].m_obj;
lean_object* v_res_1980_;
v_res_1980_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1833_, v_useDecide_1834_, v_prop_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
stack->m_obj
 = v_res_1980_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* v_numIndices_1981_, lean_object* v_useDecide_1982_, lean_object* v_prop_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
uint8_t v_useDecide_boxed_1992_; lean_object* v_res_1993_; 
v_useDecide_boxed_1992_ = lean_unbox(v_useDecide_1982_);
v_res_1993_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_1981_, v_useDecide_boxed_1992_, v_prop_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec(v_numIndices_1981_);
return v_res_1993_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(lean_object* v_cls_1994_, lean_object* v_msg_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_1994_, v_msg_1995_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1994_ = stack[0].m_obj;
lean_object* v_msg_1995_ = stack[1].m_obj;
lean_object* v___y_1996_ = stack[2].m_obj;
lean_object* v___y_1997_ = stack[3].m_obj;
lean_object* v___y_1998_ = stack[4].m_obj;
lean_object* v___y_1999_ = stack[5].m_obj;
lean_object* v___y_2000_ = stack[6].m_obj;
lean_object* v___y_2001_ = stack[7].m_obj;
lean_object* v___y_2002_ = stack[8].m_obj;
lean_object* v_res_2005_;
v_res_2005_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_1994_, v_msg_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
stack->m_obj
 = v_res_2005_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(lean_object* v_cls_2006_, lean_object* v_msg_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_2006_, v_msg_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
return v_res_2016_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(lean_object* v_numIndices_2017_, lean_object* v_a_2018_, lean_object* v_as_2019_, lean_object* v_i_2020_, lean_object* v_a_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_numIndices_2017_, v_a_2018_, v_as_2019_, v_i_2020_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_2017_ = stack[0].m_obj;
lean_object* v_a_2018_ = stack[1].m_obj;
lean_object* v_as_2019_ = stack[2].m_obj;
lean_object* v_i_2020_ = stack[3].m_obj;
lean_object* v___y_2022_ = stack[5].m_obj;
lean_object* v___y_2023_ = stack[6].m_obj;
lean_object* v___y_2024_ = stack[7].m_obj;
lean_object* v___y_2025_ = stack[8].m_obj;
lean_object* v___y_2026_ = stack[9].m_obj;
lean_object* v___y_2027_ = stack[10].m_obj;
lean_object* v___y_2028_ = stack[11].m_obj;
lean_object* v_res_2031_;
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_numIndices_2017_, v_a_2018_, v_as_2019_, v_i_2020_, lean_box(0), v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
stack->m_obj
 = v_res_2031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_numIndices_2032_, lean_object* v_a_2033_, lean_object* v_as_2034_, lean_object* v_i_2035_, lean_object* v_a_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_numIndices_2032_, v_a_2033_, v_as_2034_, v_i_2035_, v_a_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v_as_2034_);
lean_dec(v_numIndices_2032_);
return v_res_2045_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_numIndices_2046_, lean_object* v_a_2047_, lean_object* v_as_2048_, lean_object* v_i_2049_, lean_object* v_a_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_numIndices_2046_, v_a_2047_, v_as_2048_, v_i_2049_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_2046_ = stack[0].m_obj;
lean_object* v_a_2047_ = stack[1].m_obj;
lean_object* v_as_2048_ = stack[2].m_obj;
lean_object* v_i_2049_ = stack[3].m_obj;
lean_object* v___y_2051_ = stack[5].m_obj;
lean_object* v___y_2052_ = stack[6].m_obj;
lean_object* v___y_2053_ = stack[7].m_obj;
lean_object* v___y_2054_ = stack[8].m_obj;
lean_object* v___y_2055_ = stack[9].m_obj;
lean_object* v___y_2056_ = stack[10].m_obj;
lean_object* v___y_2057_ = stack[11].m_obj;
lean_object* v_res_2060_;
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_numIndices_2046_, v_a_2047_, v_as_2048_, v_i_2049_, lean_box(0), v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
stack->m_obj
 = v_res_2060_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_numIndices_2061_, lean_object* v_a_2062_, lean_object* v_as_2063_, lean_object* v_i_2064_, lean_object* v_a_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_numIndices_2061_, v_a_2062_, v_as_2063_, v_i_2064_, v_a_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v_as_2063_);
lean_dec(v_numIndices_2061_);
return v_res_2074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2));
v___x_2082_ = l_Lean_mkConst(v___x_2081_, v___x_2080_);
return v___x_2082_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(lean_object* v_numIndices_2086_, uint8_t v_useDecideBool_2087_, lean_object* v_e_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2100_; 
lean_inc_ref(v_e_2088_);
v___x_2100_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2088_, v_a_2093_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Expr_cleanupAnnotations(v_a_2101_);
v___x_2103_ = l_Lean_Expr_isApp(v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v___x_2102_);
lean_dec_ref(v_e_2088_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_arg_2104_ = lean_ctor_get(v___x_2102_, 1);
lean_inc_ref(v_arg_2104_);
v___x_2105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2102_);
v___x_2106_ = l_Lean_Expr_isApp(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___x_2105_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v_arg_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc_ref(v_arg_2107_);
v___x_2108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2105_);
v___x_2109_ = l_Lean_Expr_isApp(v___x_2108_);
if (v___x_2109_ == 0)
{
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_arg_2110_ = lean_ctor_get(v___x_2108_, 1);
lean_inc_ref(v_arg_2110_);
v___x_2111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2108_);
v___x_2112_ = l_Lean_Expr_isApp(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_dec_ref(v___x_2111_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_arg_2113_ = lean_ctor_get(v___x_2111_, 1);
lean_inc_ref(v_arg_2113_);
v___x_2114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2111_);
v___x_2115_ = l_Lean_Expr_isApp(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec_ref(v___x_2114_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v_arg_2116_ = lean_ctor_get(v___x_2114_, 1);
lean_inc_ref(v_arg_2116_);
v___x_2117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2114_);
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2));
v___x_2119_ = l_Lean_Expr_isConstOf(v___x_2117_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
goto v___jp_2097_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = l_Lean_Expr_constLevels_x21(v___x_2117_);
lean_inc_ref(v_arg_2113_);
v___x_2121_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2086_, v_useDecideBool_2087_, v_arg_2113_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2264_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2264_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2264_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
if (lean_obj_tag(v_a_2122_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_e_2088_);
v_val_2126_ = lean_ctor_get(v_a_2122_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2122_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2128_ = v_a_2122_;
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_val_2126_);
lean_dec(v_a_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2130_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__4));
v___x_2131_ = l_Lean_mkConst(v___x_2130_, v___x_2120_);
lean_inc_ref(v_arg_2107_);
v___x_2132_ = l_Lean_mkApp6(v___x_2131_, v_arg_2113_, v_arg_2110_, v_val_2126_, v_arg_2116_, v_arg_2107_, v_arg_2104_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2132_);
v___x_2134_ = v___x_2128_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2135_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2135_, 0, v_arg_2107_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*2, v___x_2119_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2136_);
v___x_2138_ = v___x_2124_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_del_object(v___x_2124_);
lean_dec(v_a_2122_);
lean_inc_ref(v_arg_2113_);
v___x_2142_ = l_Lean_mkNot(v_arg_2113_);
v___x_2143_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2086_, v_useDecideBool_2087_, v___x_2142_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2255_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2255_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2255_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_e_2088_);
v_val_2148_ = lean_ctor_get(v_a_2144_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2150_ = v_a_2144_;
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_val_2148_);
lean_dec(v_a_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2152_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__6));
v___x_2153_ = l_Lean_mkConst(v___x_2152_, v___x_2120_);
lean_inc_ref(v_arg_2104_);
v___x_2154_ = l_Lean_mkApp6(v___x_2153_, v_arg_2113_, v_arg_2110_, v_val_2148_, v_arg_2116_, v_arg_2107_, v_arg_2104_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2154_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2157_, 0, v_arg_2104_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*2, v___x_2119_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2158_);
v___x_2160_ = v___x_2146_;
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
lean_object* v___x_2164_; 
lean_del_object(v___x_2146_);
lean_dec(v_a_2144_);
lean_inc(v_a_2095_);
lean_inc_ref(v_a_2094_);
lean_inc(v_a_2093_);
lean_inc_ref(v_a_2092_);
lean_inc(v_a_2091_);
lean_inc_ref(v_a_2090_);
lean_inc(v_a_2089_);
lean_inc_ref(v_arg_2113_);
v___x_2164_ = lean_simp(v_arg_2113_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2246_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2246_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2246_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_expr_2169_; uint8_t v___x_2170_; 
v_expr_2169_ = lean_ctor_get(v_a_2165_, 0);
v___x_2170_ = lean_expr_eqv(v_expr_2169_, v_arg_2113_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_del_object(v___x_2167_);
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2169_);
v___x_2172_ = l_Lean_Expr_app___override(v___x_2171_, v_expr_2169_);
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Lean_Meta_trySynthInstance(v___x_2172_, v___x_2173_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2223_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2223_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2223_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2209_; 
lean_inc_ref(v_expr_2169_);
lean_del_object(v___x_2177_);
lean_dec_ref(v_e_2088_);
v_a_2179_ = lean_ctor_get(v_a_2175_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2175_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2181_ = v_a_2175_;
v_isShared_2182_ = v_isSharedCheck_2209_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v_a_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2209_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Meta_Simp_Result_getProof(v_a_2165_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2200_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2200_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2200_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5));
v___x_2189_ = l_Lean_mkConst(v___x_2188_, v___x_2120_);
lean_inc_ref(v_arg_2104_);
lean_inc_ref(v_arg_2107_);
lean_inc(v_a_2179_);
lean_inc_ref(v_expr_2169_);
lean_inc_ref(v_arg_2116_);
v___x_2190_ = l_Lean_mkApp8(v___x_2189_, v_arg_2116_, v_arg_2113_, v_expr_2169_, v_arg_2110_, v_a_2179_, v_arg_2107_, v_arg_2104_, v_a_2184_);
v___x_2191_ = l_Lean_mkApp5(v___x_2117_, v_arg_2116_, v_expr_2169_, v_a_2179_, v_arg_2107_, v_arg_2104_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2190_);
v___x_2193_ = v___x_2181_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2190_);
v___x_2193_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2191_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*2, v___x_2119_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2195_);
v___x_2197_ = v___x_2186_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
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
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_del_object(v___x_2181_);
lean_dec(v_a_2179_);
lean_dec_ref(v_expr_2169_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
v_a_2201_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2183_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2183_);
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
else
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2175_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; 
v_unused_2221_ = lean_ctor_get(v_a_2165_, 1);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_a_2165_, 0);
lean_dec(v_unused_2222_);
v___x_2211_ = v_a_2165_;
v_isShared_2212_ = v_isSharedCheck_2220_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v_a_2165_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2220_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2173_);
lean_ctor_set(v___x_2211_, 0, v_e_2088_);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_e_2088_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2173_);
v___x_2214_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*2, v___x_2119_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2215_);
v___x_2217_ = v___x_2177_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_a_2165_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
v_a_2224_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2174_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2174_);
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
else
{
lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; lean_object* v_unused_2245_; 
v_unused_2244_ = lean_ctor_get(v_a_2165_, 1);
lean_dec(v_unused_2244_);
v_unused_2245_ = lean_ctor_get(v_a_2165_, 0);
lean_dec(v_unused_2245_);
v___x_2233_ = v_a_2165_;
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
else
{
lean_dec(v_a_2165_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = lean_box(0);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 1, v___x_2235_);
lean_ctor_set(v___x_2233_, 0, v_e_2088_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_e_2088_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*2, v___x_2119_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2238_);
v___x_2240_ = v___x_2167_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
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
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
v_a_2247_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2164_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2164_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
v_a_2256_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2143_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2143_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_arg_2116_);
lean_dec_ref(v_arg_2113_);
lean_dec_ref(v_arg_2110_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_e_2088_);
v_a_2265_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2121_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2121_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
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
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_e_2088_);
v_a_2273_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2100_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2100_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
v___jp_2097_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_2086_ = stack[0].m_obj;
uint8_t v_useDecideBool_2087_ = stack[1].m_num;
lean_object* v_e_2088_ = stack[2].m_obj;
lean_object* v_a_2089_ = stack[3].m_obj;
lean_object* v_a_2090_ = stack[4].m_obj;
lean_object* v_a_2091_ = stack[5].m_obj;
lean_object* v_a_2092_ = stack[6].m_obj;
lean_object* v_a_2093_ = stack[7].m_obj;
lean_object* v_a_2094_ = stack[8].m_obj;
lean_object* v_a_2095_ = stack[9].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2086_, v_useDecideBool_2087_, v_e_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(lean_object* v_numIndices_2282_, lean_object* v_useDecideBool_2283_, lean_object* v_e_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
uint8_t v_useDecideBool_boxed_2293_; lean_object* v_res_2294_; 
v_useDecideBool_boxed_2293_ = lean_unbox(v_useDecideBool_2283_);
v_res_2294_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(v_numIndices_2282_, v_useDecideBool_boxed_2293_, v_e_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec(v_numIndices_2282_);
return v_res_2294_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
if (lean_obj_tag(v_e_2298_) == 6)
{
lean_object* v_binderName_2302_; lean_object* v___x_2303_; 
v_binderName_2302_ = lean_ctor_get(v_e_2298_, 0);
lean_inc(v_binderName_2302_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_binderName_2302_);
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2305_ = l_Lean_Core_mkFreshUserName(v___x_2304_, v_a_2299_, v_a_2300_);
return v___x_2305_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2298_ = stack[0].m_obj;
lean_object* v_a_2299_ = stack[1].m_obj;
lean_object* v_a_2300_ = stack[2].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2298_, v_a_2299_, v_a_2300_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(lean_object* v_e_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec_ref(v_e_2307_);
return v_res_2311_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_e_2312_, v_a_2315_, v_a_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2312_ = stack[0].m_obj;
lean_object* v_a_2313_ = stack[1].m_obj;
lean_object* v_a_2314_ = stack[2].m_obj;
lean_object* v_a_2315_ = stack[3].m_obj;
lean_object* v_a_2316_ = stack[4].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(lean_object* v_e_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec_ref(v_e_2320_);
return v_res_2326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_box(0);
v___x_2333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2));
v___x_2334_ = l_Lean_mkConst(v___x_2333_, v___x_2332_);
return v___x_2334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = l_Lean_mkBVar(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_box(0);
v___x_2342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6));
v___x_2343_ = l_Lean_mkConst(v___x_2342_, v___x_2341_);
return v___x_2343_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(lean_object* v_numIndices_2347_, uint8_t v_useDecideBool_2348_, lean_object* v_e_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___x_2361_; 
lean_inc_ref(v_e_2349_);
v___x_2361_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2349_, v_a_2354_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_Expr_cleanupAnnotations(v_a_2362_);
v___x_2364_ = l_Lean_Expr_isApp(v___x_2363_);
if (v___x_2364_ == 0)
{
lean_dec_ref(v___x_2363_);
lean_dec_ref(v_e_2349_);
goto v___jp_2358_;
}
else
{
lean_object* v_arg_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_arg_2365_ = lean_ctor_get(v___x_2363_, 1);
lean_inc_ref(v_arg_2365_);
v___x_2366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2363_);
v___x_2367_ = l_Lean_Expr_isApp(v___x_2366_);
if (v___x_2367_ == 0)
{
lean_dec_ref(v___x_2366_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
goto v___jp_2358_;
}
else
{
lean_object* v_arg_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_arg_2368_ = lean_ctor_get(v___x_2366_, 1);
lean_inc_ref(v_arg_2368_);
v___x_2369_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2366_);
v___x_2370_ = l_Lean_Expr_isApp(v___x_2369_);
if (v___x_2370_ == 0)
{
lean_dec_ref(v___x_2369_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
goto v___jp_2358_;
}
else
{
lean_object* v_arg_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v_arg_2371_ = lean_ctor_get(v___x_2369_, 1);
lean_inc_ref(v_arg_2371_);
v___x_2372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2369_);
v___x_2373_ = l_Lean_Expr_isApp(v___x_2372_);
if (v___x_2373_ == 0)
{
lean_dec_ref(v___x_2372_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
goto v___jp_2358_;
}
else
{
lean_object* v_arg_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_arg_2374_ = lean_ctor_get(v___x_2372_, 1);
lean_inc_ref(v_arg_2374_);
v___x_2375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2372_);
v___x_2376_ = l_Lean_Expr_isApp(v___x_2375_);
if (v___x_2376_ == 0)
{
lean_dec_ref(v___x_2375_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
goto v___jp_2358_;
}
else
{
lean_object* v_arg_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_arg_2377_ = lean_ctor_get(v___x_2375_, 1);
lean_inc_ref(v_arg_2377_);
v___x_2378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2375_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4));
v___x_2380_ = l_Lean_Expr_isConstOf(v___x_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
goto v___jp_2358_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = l_Lean_Expr_constLevels_x21(v___x_2378_);
lean_inc_ref(v_arg_2374_);
v___x_2382_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2347_, v_useDecideBool_2348_, v_arg_2374_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2554_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2554_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2554_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
if (lean_obj_tag(v_a_2383_) == 1)
{
lean_object* v_val_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_e_2349_);
v_val_2387_ = lean_ctor_get(v_a_2383_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_a_2383_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2389_ = v_a_2383_;
v_isShared_2390_ = v_isSharedCheck_2404_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_val_2387_);
lean_dec(v_a_2383_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2404_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_inc(v_val_2387_);
lean_inc_ref(v_arg_2368_);
v___x_2391_ = l_Lean_Expr_app___override(v_arg_2368_, v_val_2387_);
v___x_2392_ = l_Lean_Expr_headBeta(v___x_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__8));
v___x_2394_ = l_Lean_mkConst(v___x_2393_, v___x_2381_);
v___x_2395_ = l_Lean_mkApp6(v___x_2394_, v_arg_2374_, v_arg_2371_, v_val_2387_, v_arg_2377_, v_arg_2368_, v_arg_2365_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2395_);
v___x_2397_ = v___x_2389_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2398_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2398_, 0, v___x_2392_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*2, v___x_2380_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2399_);
v___x_2401_ = v___x_2385_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_del_object(v___x_2385_);
lean_dec(v_a_2383_);
lean_inc_ref(v_arg_2374_);
v___x_2405_ = l_Lean_mkNot(v_arg_2374_);
v___x_2406_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_2347_, v_useDecideBool_2348_, v___x_2405_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2545_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2545_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2545_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
if (lean_obj_tag(v_a_2407_) == 1)
{
lean_object* v_val_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_e_2349_);
v_val_2411_ = lean_ctor_get(v_a_2407_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_a_2407_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2413_ = v_a_2407_;
v_isShared_2414_ = v_isSharedCheck_2428_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_val_2411_);
lean_dec(v_a_2407_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2428_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
lean_inc(v_val_2411_);
lean_inc_ref(v_arg_2365_);
v___x_2415_ = l_Lean_Expr_app___override(v_arg_2365_, v_val_2411_);
v___x_2416_ = l_Lean_Expr_headBeta(v___x_2415_);
v___x_2417_ = ((lean_object*)(l_Lean_Meta_SplitIf_getSimpContext___closed__10));
v___x_2418_ = l_Lean_mkConst(v___x_2417_, v___x_2381_);
v___x_2419_ = l_Lean_mkApp6(v___x_2418_, v_arg_2374_, v_arg_2371_, v_val_2411_, v_arg_2377_, v_arg_2368_, v_arg_2365_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2419_);
v___x_2421_ = v___x_2413_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2422_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2416_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*2, v___x_2380_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2423_);
v___x_2425_ = v___x_2409_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v___x_2429_; 
lean_del_object(v___x_2409_);
lean_dec(v_a_2407_);
lean_inc(v_a_2356_);
lean_inc_ref(v_a_2355_);
lean_inc(v_a_2354_);
lean_inc_ref(v_a_2353_);
lean_inc(v_a_2352_);
lean_inc_ref(v_a_2351_);
lean_inc(v_a_2350_);
lean_inc_ref(v_arg_2374_);
v___x_2429_ = lean_simp(v_arg_2374_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2536_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2536_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2536_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_expr_2434_; uint8_t v___x_2435_; 
v_expr_2434_ = lean_ctor_get(v_a_2430_, 0);
v___x_2435_ = lean_expr_eqv(v_expr_2434_, v_arg_2374_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; 
lean_inc_ref(v_expr_2434_);
lean_del_object(v___x_2432_);
v___x_2436_ = l_Lean_Meta_Simp_Result_getProof(v_a_2430_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
lean_inc_ref(v_expr_2434_);
v___x_2439_ = l_Lean_Expr_app___override(v___x_2438_, v_expr_2434_);
v___x_2440_ = lean_box(0);
v___x_2441_ = l_Lean_Meta_trySynthInstance(v___x_2439_, v___x_2440_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2505_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2505_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2505_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
if (lean_obj_tag(v_a_2442_) == 1)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2499_; 
lean_del_object(v___x_2444_);
lean_dec_ref(v_e_2349_);
v_a_2446_ = lean_ctor_get(v_a_2442_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2442_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2448_ = v_a_2442_;
v_isShared_2449_ = v_isSharedCheck_2499_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v_a_2442_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2499_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
v___x_2451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
lean_inc(v_a_2437_);
lean_inc_ref(v_expr_2434_);
lean_inc_ref(v_arg_2374_);
v___x_2452_ = l_Lean_mkApp4(v___x_2450_, v_arg_2374_, v_expr_2434_, v_a_2437_, v___x_2451_);
lean_inc_ref(v_arg_2368_);
v___x_2453_ = l_Lean_Expr_app___override(v_arg_2368_, v___x_2452_);
v___x_2454_ = l_Lean_Expr_headBeta(v___x_2453_);
v___x_2455_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2368_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = 0;
lean_inc_ref_n(v_expr_2434_, 2);
v___x_2458_ = l_Lean_mkLambda(v_a_2456_, v___x_2457_, v_expr_2434_, v___x_2454_);
v___x_2459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
lean_inc(v_a_2437_);
lean_inc_ref(v_arg_2374_);
v___x_2460_ = l_Lean_mkApp4(v___x_2459_, v_arg_2374_, v_expr_2434_, v_a_2437_, v___x_2451_);
lean_inc_ref(v_arg_2365_);
v___x_2461_ = l_Lean_Expr_app___override(v_arg_2365_, v___x_2460_);
v___x_2462_ = l_Lean_Expr_headBeta(v___x_2461_);
v___x_2463_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_2365_, v_a_2355_, v_a_2356_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2482_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2482_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2482_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_inc_ref_n(v_expr_2434_, 2);
v___x_2468_ = l_Lean_mkNot(v_expr_2434_);
v___x_2469_ = l_Lean_mkLambda(v_a_2464_, v___x_2457_, v___x_2468_, v___x_2462_);
lean_inc(v_a_2446_);
lean_inc_ref(v_arg_2377_);
v___x_2470_ = l_Lean_mkApp5(v___x_2378_, v_arg_2377_, v_expr_2434_, v_a_2446_, v___x_2458_, v___x_2469_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9));
v___x_2472_ = l_Lean_mkConst(v___x_2471_, v___x_2381_);
v___x_2473_ = l_Lean_mkApp8(v___x_2472_, v_arg_2377_, v_arg_2374_, v_expr_2434_, v_arg_2371_, v_a_2446_, v_arg_2368_, v_arg_2365_, v_a_2437_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2473_);
v___x_2475_ = v___x_2448_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2476_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2476_, 0, v___x_2470_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*2, v___x_2380_);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2477_);
v___x_2479_ = v___x_2466_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v___x_2462_);
lean_dec_ref(v___x_2458_);
lean_del_object(v___x_2448_);
lean_dec(v_a_2446_);
lean_dec(v_a_2437_);
lean_dec_ref(v_expr_2434_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
v_a_2483_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2463_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2463_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v___x_2454_);
lean_del_object(v___x_2448_);
lean_dec(v_a_2446_);
lean_dec(v_a_2437_);
lean_dec_ref(v_expr_2434_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
v_a_2491_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2455_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2455_);
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
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_dec(v_a_2442_);
lean_dec(v_a_2437_);
lean_dec_ref(v_expr_2434_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
v___x_2500_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2500_, 0, v_e_2349_);
lean_ctor_set(v___x_2500_, 1, v___x_2440_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*2, v___x_2380_);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2501_);
v___x_2503_ = v___x_2444_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2437_);
lean_dec_ref(v_expr_2434_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
v_a_2506_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2441_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2441_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v_expr_2434_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
v_a_2514_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2436_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2436_);
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
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2430_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; lean_object* v_unused_2535_; 
v_unused_2534_ = lean_ctor_get(v_a_2430_, 1);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_a_2430_, 0);
lean_dec(v_unused_2535_);
v___x_2523_ = v_a_2430_;
v_isShared_2524_ = v_isSharedCheck_2533_;
goto v_resetjp_2522_;
}
else
{
lean_dec(v_a_2430_);
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
lean_ctor_set(v___x_2523_, 0, v_e_2349_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_e_2349_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2, v___x_2380_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2528_);
v___x_2530_ = v___x_2432_;
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
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
v_a_2537_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2429_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2429_);
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
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
v_a_2546_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2406_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2406_);
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
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_arg_2377_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_arg_2371_);
lean_dec_ref(v_arg_2368_);
lean_dec_ref(v_arg_2365_);
lean_dec_ref(v_e_2349_);
v_a_2555_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2382_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2382_);
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
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_e_2349_);
v_a_2563_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2361_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2361_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
v___jp_2358_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0));
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_2347_ = stack[0].m_obj;
uint8_t v_useDecideBool_2348_ = stack[1].m_num;
lean_object* v_e_2349_ = stack[2].m_obj;
lean_object* v_a_2350_ = stack[3].m_obj;
lean_object* v_a_2351_ = stack[4].m_obj;
lean_object* v_a_2352_ = stack[5].m_obj;
lean_object* v_a_2353_ = stack[6].m_obj;
lean_object* v_a_2354_ = stack[7].m_obj;
lean_object* v_a_2355_ = stack[8].m_obj;
lean_object* v_a_2356_ = stack[9].m_obj;
lean_object* v_res_2571_;
v_res_2571_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2347_, v_useDecideBool_2348_, v_e_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
stack->m_obj
 = v_res_2571_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(lean_object* v_numIndices_2572_, lean_object* v_useDecideBool_2573_, lean_object* v_e_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
uint8_t v_useDecideBool_boxed_2583_; lean_object* v_res_2584_; 
v_useDecideBool_boxed_2583_ = lean_unbox(v_useDecideBool_2573_);
v_res_2584_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(v_numIndices_2572_, v_useDecideBool_boxed_2583_, v_e_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v_s_2587_; 
v___x_2585_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
v___x_2586_ = lean_obj_once(&l_Lean_Meta_SplitIf_getSimpContext___closed__0, &l_Lean_Meta_SplitIf_getSimpContext___closed__0_once, _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0);
v_s_2587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_s_2587_, 0, v___x_2586_);
lean_ctor_set(v_s_2587_, 1, v___x_2586_);
lean_ctor_set(v_s_2587_, 2, v___x_2585_);
lean_ctor_set(v_s_2587_, 3, v___x_2585_);
return v_s_2587_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(lean_object* v_numIndices_2651_, uint8_t v_useDecide_2652_){
_start:
{
lean_object* v_s_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_s_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v_s_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_s_2654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2));
v___x_2656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15));
v___x_2657_ = 0;
v___x_2658_ = lean_box(v_useDecide_2652_);
lean_inc(v_numIndices_2651_);
v___x_2659_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2659_, 0, v_numIndices_2651_);
lean_closure_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
v_s_2661_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2654_, v___x_2655_, v___x_2656_, v___x_2657_, v___x_2660_);
v___x_2662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17));
v___x_2663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19));
v___x_2664_ = lean_box(v_useDecide_2652_);
v___x_2665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed), 11, 2);
lean_closure_set(v___x_2665_, 0, v_numIndices_2651_);
lean_closure_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
v_s_2667_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2661_, v___x_2662_, v___x_2663_, v___x_2657_, v___x_2666_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_mk_empty_array_with_capacity(v___x_2668_);
v___x_2670_ = lean_array_push(v___x_2669_, v_s_2667_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_2651_ = stack[0].m_obj;
uint8_t v_useDecide_2652_ = stack[1].m_num;
lean_object* v_res_2672_;
v_res_2672_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2651_, v_useDecide_2652_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(lean_object* v_numIndices_2673_, lean_object* v_useDecide_2674_, lean_object* v_a_2675_){
_start:
{
uint8_t v_useDecide_boxed_2676_; lean_object* v_res_2677_; 
v_useDecide_boxed_2676_ = lean_unbox(v_useDecide_2674_);
v_res_2677_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2673_, v_useDecide_boxed_2676_);
return v_res_2677_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(lean_object* v_numIndices_2678_, uint8_t v_useDecide_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_numIndices_2678_, v_useDecide_2679_);
return v___x_2685_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_2678_ = stack[0].m_obj;
uint8_t v_useDecide_2679_ = stack[1].m_num;
lean_object* v_a_2680_ = stack[2].m_obj;
lean_object* v_a_2681_ = stack[3].m_obj;
lean_object* v_a_2682_ = stack[4].m_obj;
lean_object* v_a_2683_ = stack[5].m_obj;
lean_object* v_res_2686_;
v_res_2686_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2678_, v_useDecide_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
stack->m_obj
 = v_res_2686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(lean_object* v_numIndices_2687_, lean_object* v_useDecide_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
uint8_t v_useDecide_boxed_2694_; lean_object* v_res_2695_; 
v_useDecide_boxed_2694_ = lean_unbox(v_useDecide_2688_);
v_res_2695_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(v_numIndices_2687_, v_useDecide_boxed_2694_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2695_;
}
}
lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t v_useDecide_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_lctx_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_lctx_2699_ = lean_ctor_get(v_a_2697_, 2);
lean_inc_ref(v_lctx_2699_);
v___x_2700_ = lean_local_ctx_num_indices(v_lctx_2699_);
v___x_2701_ = lean_box(v_useDecide_2696_);
v___x_2702_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(v___x_2702_, 0, v___x_2700_);
lean_closure_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_useDecide_2696_ = stack[0].m_num;
lean_object* v_a_2697_ = stack[1].m_obj;
lean_object* v_res_2704_;
v_res_2704_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2696_, v_a_2697_);
stack->m_obj
 = v_res_2704_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* v_useDecide_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
uint8_t v_useDecide_boxed_2708_; lean_object* v_res_2709_; 
v_useDecide_boxed_2708_ = lean_unbox(v_useDecide_2705_);
v_res_2709_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_2708_, v_a_2706_);
lean_dec_ref(v_a_2706_);
return v_res_2709_;
}
}
lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t v_useDecide_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_2710_, v_a_2711_);
return v___x_2716_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitIf_mkDischarge_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_useDecide_2710_ = stack[0].m_num;
lean_object* v_a_2711_ = stack[1].m_obj;
lean_object* v_a_2712_ = stack[2].m_obj;
lean_object* v_a_2713_ = stack[3].m_obj;
lean_object* v_a_2714_ = stack[4].m_obj;
lean_object* v_res_2717_;
v_res_2717_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
stack->m_obj
 = v_res_2717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* v_useDecide_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
uint8_t v_useDecide_boxed_2724_; lean_object* v_res_2725_; 
v_useDecide_boxed_2724_ = lean_unbox(v_useDecide_2718_);
v_res_2725_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(v_useDecide_boxed_2724_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
return v_res_2725_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(lean_object* v_mvarId_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
v_a_2742_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2733_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2733_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2726_ = stack[0].m_obj;
lean_object* v_x_2727_ = stack[1].m_obj;
lean_object* v___y_2728_ = stack[2].m_obj;
lean_object* v___y_2729_ = stack[3].m_obj;
lean_object* v___y_2730_ = stack[4].m_obj;
lean_object* v___y_2731_ = stack[5].m_obj;
lean_object* v_res_2750_;
v_res_2750_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
stack->m_obj
 = v_res_2750_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_2751_, lean_object* v_x_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2751_, v_x_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_object* v_00_u03b1_2759_, lean_object* v_mvarId_2760_, lean_object* v_x_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2760_, v_x_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2760_ = stack[1].m_obj;
lean_object* v_x_2761_ = stack[2].m_obj;
lean_object* v___y_2762_ = stack[3].m_obj;
lean_object* v___y_2763_ = stack[4].m_obj;
lean_object* v___y_2764_ = stack[5].m_obj;
lean_object* v___y_2765_ = stack[6].m_obj;
lean_object* v_res_2768_;
v_res_2768_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(lean_box(0), v_mvarId_2760_, v_x_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
stack->m_obj
 = v_res_2768_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2769_, lean_object* v_mvarId_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(v_00_u03b1_2769_, v_mvarId_2770_, v_x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2777_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
static lean_object* _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2));
v___x_2783_ = l_Lean_stringToMessageData(v___x_2782_);
return v___x_2783_;
}
}
lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* v_e_2784_, lean_object* v_mvarId_2785_, lean_object* v_hName_x3f_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2795_; lean_object* v_a_2796_; lean_object* v___x_2797_; 
v___x_2795_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(v_e_2784_, v___y_2788_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc_n(v_a_2796_, 2);
lean_dec_ref(v___x_2795_);
v___x_2797_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(v_a_2796_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
if (lean_obj_tag(v_a_2798_) == 1)
{
lean_object* v_val_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_a_2796_);
v_val_2799_ = lean_ctor_get(v_a_2798_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2801_ = v_a_2798_;
v_isShared_2802_ = v_isSharedCheck_2874_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_val_2799_);
lean_dec(v_a_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2874_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2873_; 
v_fst_2803_ = lean_ctor_get(v_val_2799_, 0);
v_snd_2804_ = lean_ctor_get(v_val_2799_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_val_2799_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2806_ = v_val_2799_;
v_isShared_2807_ = v_isSharedCheck_2873_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_snd_2804_);
lean_inc(v_fst_2803_);
lean_dec(v_val_2799_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2873_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v_hName_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; 
if (lean_obj_tag(v_hName_x3f_2786_) == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1));
v___x_2862_ = l_Lean_Core_mkFreshUserName(v___x_2861_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v_hName_2835_ = v_a_2863_;
v___y_2836_ = v___y_2787_;
v___y_2837_ = v___y_2788_;
v___y_2838_ = v___y_2789_;
v___y_2839_ = v___y_2790_;
goto v___jp_2834_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_del_object(v___x_2806_);
lean_dec(v_snd_2804_);
lean_dec(v_fst_2803_);
lean_del_object(v___x_2801_);
lean_dec(v_mvarId_2785_);
v_a_2864_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2862_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_val_2872_; 
v_val_2872_ = lean_ctor_get(v_hName_x3f_2786_, 0);
lean_inc(v_val_2872_);
lean_dec_ref_known(v_hName_x3f_2786_, 1);
v_hName_2835_ = v_val_2872_;
v___y_2836_ = v___y_2787_;
v___y_2837_ = v___y_2788_;
v___y_2838_ = v___y_2789_;
v___y_2839_ = v___y_2790_;
goto v___jp_2834_;
}
v___jp_2808_:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_MVarId_byCasesDec(v_mvarId_2785_, v_fst_2803_, v_snd_2804_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2825_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2825_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2825_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_a_2815_);
v___x_2820_ = v___x_2801_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2820_);
v___x_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_del_object(v___x_2801_);
v_a_2826_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2814_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2814_);
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
v___jp_2834_:
{
lean_object* v_toCold_2840_; lean_object* v_options_2841_; uint8_t v_hasTrace_2842_; 
v_toCold_2840_ = lean_ctor_get(v___y_2838_, 0);
v_options_2841_ = lean_ctor_get(v_toCold_2840_, 2);
v_hasTrace_2842_ = lean_ctor_get_uint8(v_options_2841_, sizeof(void*)*1);
if (v_hasTrace_2842_ == 0)
{
lean_del_object(v___x_2806_);
v___y_2809_ = v_hName_2835_;
v___y_2810_ = v___y_2836_;
v___y_2811_ = v___y_2837_;
v___y_2812_ = v___y_2838_;
v___y_2813_ = v___y_2839_;
goto v___jp_2808_;
}
else
{
lean_object* v_inheritedTraceOptions_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_inheritedTraceOptions_2843_ = lean_ctor_get(v_toCold_2840_, 11);
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2843_, v_options_2841_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_del_object(v___x_2806_);
v___y_2809_ = v_hName_2835_;
v___y_2810_ = v___y_2836_;
v___y_2811_ = v___y_2837_;
v___y_2812_ = v___y_2838_;
v___y_2813_ = v___y_2839_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2847_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1);
lean_inc(v_snd_2804_);
v___x_2848_ = l_Lean_MessageData_ofExpr(v_snd_2804_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set_tag(v___x_2806_, 7);
lean_ctor_set(v___x_2806_, 1, v___x_2848_);
lean_ctor_set(v___x_2806_, 0, v___x_2847_);
v___x_2850_ = v___x_2806_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2844_, v___x_2850_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
v___y_2809_ = v_hName_2835_;
v___y_2810_ = v___y_2836_;
v___y_2811_ = v___y_2837_;
v___y_2812_ = v___y_2838_;
v___y_2813_ = v___y_2839_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_hName_2835_);
lean_dec(v_snd_2804_);
lean_dec(v_fst_2803_);
lean_del_object(v___x_2801_);
lean_dec(v_mvarId_2785_);
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
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
lean_object* v_toCold_2875_; lean_object* v_options_2876_; uint8_t v_hasTrace_2877_; 
lean_dec(v_a_2798_);
lean_dec(v_hName_x3f_2786_);
lean_dec(v_mvarId_2785_);
v_toCold_2875_ = lean_ctor_get(v___y_2789_, 0);
v_options_2876_ = lean_ctor_get(v_toCold_2875_, 2);
v_hasTrace_2877_ = lean_ctor_get_uint8(v_options_2876_, sizeof(void*)*1);
if (v_hasTrace_2877_ == 0)
{
lean_dec(v_a_2796_);
goto v___jp_2792_;
}
else
{
lean_object* v_inheritedTraceOptions_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v_inheritedTraceOptions_2878_ = lean_ctor_get(v_toCold_2875_, 11);
v___x_2879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_2880_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10);
v___x_2881_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2878_, v_options_2876_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_dec(v_a_2796_);
goto v___jp_2792_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2882_ = lean_obj_once(&l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3, &l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3);
v___x_2883_ = l_Lean_indentExpr(v_a_2796_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_2879_, v___x_2884_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_dec_ref_known(v___x_2885_, 1);
goto v___jp_2792_;
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_a_2796_);
lean_dec(v_hName_x3f_2786_);
lean_dec(v_mvarId_2785_);
v_a_2894_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2797_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2797_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
v___jp_2792_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2784_ = stack[0].m_obj;
lean_object* v_mvarId_2785_ = stack[1].m_obj;
lean_object* v_hName_x3f_2786_ = stack[2].m_obj;
lean_object* v___y_2787_ = stack[3].m_obj;
lean_object* v___y_2788_ = stack[4].m_obj;
lean_object* v___y_2789_ = stack[5].m_obj;
lean_object* v___y_2790_ = stack[6].m_obj;
lean_object* v_res_2902_;
v_res_2902_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2784_, v_mvarId_2785_, v_hName_x3f_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
stack->m_obj
 = v_res_2902_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(lean_object* v_e_2903_, lean_object* v_mvarId_2904_, lean_object* v_hName_x3f_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(v_e_2903_, v_mvarId_2904_, v_hName_x3f_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2911_;
}
}
lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* v_mvarId_2912_, lean_object* v_e_2913_, lean_object* v_hName_x3f_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___f_2920_; lean_object* v___x_2921_; 
lean_inc(v_mvarId_2912_);
v___f_2920_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2920_, 0, v_e_2913_);
lean_closure_set(v___f_2920_, 1, v_mvarId_2912_);
lean_closure_set(v___f_2920_, 2, v_hName_x3f_2914_);
v___x_2921_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2912_, v___f_2920_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
return v___x_2921_;
}
}
LEAN_EXPORT void l_Lean_Meta_SplitIf_splitIfAt_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2912_ = stack[0].m_obj;
lean_object* v_e_2913_ = stack[1].m_obj;
lean_object* v_hName_x3f_2914_ = stack[2].m_obj;
lean_object* v_a_2915_ = stack[3].m_obj;
lean_object* v_a_2916_ = stack[4].m_obj;
lean_object* v_a_2917_ = stack[5].m_obj;
lean_object* v_a_2918_ = stack[6].m_obj;
lean_object* v_res_2922_;
v_res_2922_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2912_, v_e_2913_, v_hName_x3f_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
stack->m_obj
 = v_res_2922_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* v_mvarId_2923_, lean_object* v_e_2924_, lean_object* v_hName_x3f_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_2923_, v_e_2924_, v_hName_x3f_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2931_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_lctx_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_lctx_2937_ = lean_ctor_get(v___y_2932_, 2);
lean_inc_ref(v_lctx_2937_);
lean_dec_ref(v___y_2932_);
v___x_2938_ = lean_local_ctx_num_indices(v_lctx_2937_);
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2932_ = stack[0].m_obj;
lean_object* v___y_2933_ = stack[1].m_obj;
lean_object* v___y_2934_ = stack[2].m_obj;
lean_object* v___y_2935_ = stack[3].m_obj;
lean_object* v_res_2940_;
v_res_2940_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
stack->m_obj
 = v_res_2940_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
return v_res_2946_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(lean_object* v_mvarId_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0));
v___x_2955_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_2948_, v___f_2954_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2955_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2948_ = stack[0].m_obj;
lean_object* v_a_2949_ = stack[1].m_obj;
lean_object* v_a_2950_ = stack[2].m_obj;
lean_object* v_a_2951_ = stack[3].m_obj;
lean_object* v_a_2952_ = stack[4].m_obj;
lean_object* v_res_2956_;
v_res_2956_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
stack->m_obj
 = v_res_2956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(lean_object* v_mvarId_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
lean_dec(v_a_2961_);
lean_dec_ref(v_a_2960_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
return v_res_2963_;
}
}
lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0(lean_object* v_msg_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___f_2971_; lean_object* v___x_1613__overap_2972_; lean_object* v___x_2973_; 
v___f_2971_ = ((lean_object*)(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0));
v___x_1613__overap_2972_ = lean_panic_fn_borrowed(v___f_2971_, v_msg_2965_);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___x_2973_ = lean_apply_5(v___x_1613__overap_2972_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, lean_box(0));
return v___x_2973_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_simpIfTarget_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2965_ = stack[0].m_obj;
lean_object* v___y_2966_ = stack[1].m_obj;
lean_object* v___y_2967_ = stack[2].m_obj;
lean_object* v___y_2968_ = stack[3].m_obj;
lean_object* v___y_2969_ = stack[4].m_obj;
lean_object* v_res_2974_;
v_res_2974_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
stack->m_obj
 = v_res_2974_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(lean_object* v_msg_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v_msg_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
return v_res_2981_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(lean_object* v_opts_2982_, lean_object* v_opt_2983_){
_start:
{
lean_object* v_name_2984_; lean_object* v_defValue_2985_; lean_object* v_map_2986_; lean_object* v___x_2987_; 
v_name_2984_ = lean_ctor_get(v_opt_2983_, 0);
v_defValue_2985_ = lean_ctor_get(v_opt_2983_, 1);
v_map_2986_ = lean_ctor_get(v_opts_2982_, 0);
v___x_2987_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2986_, v_name_2984_);
if (lean_obj_tag(v___x_2987_) == 0)
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_unbox(v_defValue_2985_);
return v___x_2988_;
}
else
{
lean_object* v_val_2989_; 
v_val_2989_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_val_2989_);
lean_dec_ref_known(v___x_2987_, 1);
if (lean_obj_tag(v_val_2989_) == 1)
{
uint8_t v_v_2990_; 
v_v_2990_ = lean_ctor_get_uint8(v_val_2989_, 0);
lean_dec_ref_known(v_val_2989_, 0);
return v_v_2990_;
}
else
{
uint8_t v___x_2991_; 
lean_dec(v_val_2989_);
v___x_2991_ = lean_unbox(v_defValue_2985_);
return v___x_2991_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2982_ = stack[0].m_obj;
lean_object* v_opt_2983_ = stack[1].m_obj;
uint8_t v_res_2992_;
v_res_2992_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2982_, v_opt_2983_);
stack->m_num = v_res_2992_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(lean_object* v_opts_2993_, lean_object* v_opt_2994_){
_start:
{
uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_res_2995_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_2993_, v_opt_2994_);
lean_dec_ref(v_opt_2994_);
lean_dec_ref(v_opts_2993_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__0(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___redArg___closed__0);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__1(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2999_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__2(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_unsigned_to_nat(32u);
v___x_3003_ = lean_mk_empty_array_with_capacity(v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__3(void){
_start:
{
size_t v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3005_ = ((size_t)5ULL);
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_unsigned_to_nat(32u);
v___x_3008_ = lean_mk_empty_array_with_capacity(v___x_3007_);
v___x_3009_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__2, &l_Lean_Meta_simpIfTarget___closed__2_once, _init_l_Lean_Meta_simpIfTarget___closed__2);
v___x_3010_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3008_);
lean_ctor_set(v___x_3010_, 2, v___x_3006_);
lean_ctor_set(v___x_3010_, 3, v___x_3006_);
lean_ctor_set_usize(v___x_3010_, 4, v___x_3005_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__4(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__3, &l_Lean_Meta_simpIfTarget___closed__3_once, _init_l_Lean_Meta_simpIfTarget___closed__3);
v___x_3012_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__0, &l_Lean_Meta_simpIfTarget___closed__0_once, _init_l_Lean_Meta_simpIfTarget___closed__0);
v___x_3013_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
lean_ctor_set(v___x_3013_, 3, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__5(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__4, &l_Lean_Meta_simpIfTarget___closed__4_once, _init_l_Lean_Meta_simpIfTarget___closed__4);
v___x_3015_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__1, &l_Lean_Meta_simpIfTarget___closed__1_once, _init_l_Lean_Meta_simpIfTarget___closed__1);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___x_3014_);
return v___x_3016_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__9(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3020_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3021_ = lean_unsigned_to_nat(78u);
v___x_3022_ = lean_unsigned_to_nat(289u);
v___x_3023_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3024_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_3025_ = l_mkPanicMessageWithDecl(v___x_3024_, v___x_3023_, v___x_3022_, v___x_3021_, v___x_3020_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfTarget___closed__11(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3028_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3029_ = lean_unsigned_to_nat(128u);
v___x_3030_ = lean_unsigned_to_nat(293u);
v___x_3031_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__7));
v___x_3032_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_3033_ = l_mkPanicMessageWithDecl(v___x_3032_, v___x_3031_, v___x_3030_, v___x_3029_, v___x_3028_);
return v___x_3033_;
}
}
lean_object* l_Lean_Meta_simpIfTarget(lean_object* v_mvarId_3034_, uint8_t v_useDecide_3035_, uint8_t v_useNewSemantics_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
if (v_useNewSemantics_3036_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3089_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3039_);
v___x_3090_ = l_Lean_Meta_backward_split;
v___x_3091_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v___x_3089_, v___x_3090_);
lean_dec_ref(v___x_3089_);
if (v___x_3091_ == 0)
{
goto v___jp_3042_;
}
else
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = lean_box(v_useDecide_3035_);
v___x_3095_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3095_, 0, v___x_3094_);
lean_inc(v_mvarId_3034_);
v___x_3096_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3034_, v___x_3095_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__10));
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_a_3097_);
v___x_3100_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3101_ = l_Lean_Meta_simpTarget(v_mvarId_3034_, v_a_3093_, v___x_3098_, v___x_3099_, v_useNewSemantics_3036_, v___x_3100_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3113_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3113_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3113_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v_fst_3106_; 
v_fst_3106_ = lean_ctor_get(v_a_3102_, 0);
lean_inc(v_fst_3106_);
lean_dec(v_a_3102_);
if (lean_obj_tag(v_fst_3106_) == 1)
{
lean_object* v_val_3107_; lean_object* v___x_3109_; 
v_val_3107_ = lean_ctor_get(v_fst_3106_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v_fst_3106_, 1);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v_val_3107_);
v___x_3109_ = v___x_3104_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_val_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v_fst_3106_);
lean_del_object(v___x_3104_);
v___x_3111_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__11, &l_Lean_Meta_simpIfTarget___closed__11_once, _init_l_Lean_Meta_simpIfTarget___closed__11);
v___x_3112_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3111_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3112_;
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
v_a_3114_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3101_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3101_);
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
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_a_3093_);
lean_dec(v_mvarId_3034_);
v_a_3122_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3096_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3096_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v_mvarId_3034_);
v_a_3130_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3092_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3092_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
else
{
goto v___jp_3042_;
}
v___jp_3042_:
{
lean_object* v___x_3043_; 
v___x_3043_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3037_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
lean_inc(v_mvarId_3034_);
v___x_3045_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3034_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; lean_object* v_a_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3046_, v_useDecide_3035_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = lean_box(0);
v___x_3050_ = 0;
v___x_3051_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3052_ = l_Lean_Meta_simpTarget(v_mvarId_3034_, v_a_3044_, v_a_3048_, v___x_3049_, v___x_3050_, v___x_3051_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3064_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3064_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3064_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_fst_3057_; 
v_fst_3057_ = lean_ctor_get(v_a_3053_, 0);
lean_inc(v_fst_3057_);
lean_dec(v_a_3053_);
if (lean_obj_tag(v_fst_3057_) == 1)
{
lean_object* v_val_3058_; lean_object* v___x_3060_; 
v_val_3058_ = lean_ctor_get(v_fst_3057_, 0);
lean_inc(v_val_3058_);
lean_dec_ref_known(v_fst_3057_, 1);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v_val_3058_);
v___x_3060_ = v___x_3055_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_val_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_dec(v_fst_3057_);
lean_del_object(v___x_3055_);
v___x_3062_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__9, &l_Lean_Meta_simpIfTarget___closed__9_once, _init_l_Lean_Meta_simpIfTarget___closed__9);
v___x_3063_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3062_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3063_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
v_a_3065_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3052_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3052_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v_a_3044_);
lean_dec(v_mvarId_3034_);
v_a_3073_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3045_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3045_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_mvarId_3034_);
v_a_3081_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3043_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3043_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_simpIfTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3034_ = stack[0].m_obj;
uint8_t v_useDecide_3035_ = stack[1].m_num;
uint8_t v_useNewSemantics_3036_ = stack[2].m_num;
lean_object* v_a_3037_ = stack[3].m_obj;
lean_object* v_a_3038_ = stack[4].m_obj;
lean_object* v_a_3039_ = stack[5].m_obj;
lean_object* v_a_3040_ = stack[6].m_obj;
lean_object* v_res_3138_;
v_res_3138_ = l_Lean_Meta_simpIfTarget(v_mvarId_3034_, v_useDecide_3035_, v_useNewSemantics_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
stack->m_obj
 = v_res_3138_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* v_mvarId_3139_, lean_object* v_useDecide_3140_, lean_object* v_useNewSemantics_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
uint8_t v_useDecide_boxed_3147_; uint8_t v_useNewSemantics_boxed_3148_; lean_object* v_res_3149_; 
v_useDecide_boxed_3147_ = lean_unbox(v_useDecide_3140_);
v_useNewSemantics_boxed_3148_ = lean_unbox(v_useNewSemantics_3141_);
v_res_3149_ = l_Lean_Meta_simpIfTarget(v_mvarId_3139_, v_useDecide_boxed_3147_, v_useNewSemantics_boxed_3148_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
return v_res_3149_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3151_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3152_ = lean_unsigned_to_nat(93u);
v___x_3153_ = lean_unsigned_to_nat(305u);
v___x_3154_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3155_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_3156_ = l_mkPanicMessageWithDecl(v___x_3155_, v___x_3154_, v___x_3153_, v___x_3152_, v___x_3151_);
return v___x_3156_;
}
}
static lean_object* _init_l_Lean_Meta_simpIfLocalDecl___closed__2(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3157_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__8));
v___x_3158_ = lean_unsigned_to_nat(133u);
v___x_3159_ = lean_unsigned_to_nat(309u);
v___x_3160_ = ((lean_object*)(l_Lean_Meta_simpIfLocalDecl___closed__0));
v___x_3161_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__6));
v___x_3162_ = l_mkPanicMessageWithDecl(v___x_3161_, v___x_3160_, v___x_3159_, v___x_3158_, v___x_3157_);
return v___x_3162_;
}
}
lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* v_mvarId_3163_, lean_object* v_fvarId_3164_, uint8_t v_useNewSemantics_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
if (v_useNewSemantics_3165_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3219_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3168_);
v___x_3220_ = l_Lean_Meta_backward_split;
v___x_3221_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v___x_3219_, v___x_3220_);
lean_dec_ref(v___x_3219_);
if (v___x_3221_ == 0)
{
goto v___jp_3171_;
}
else
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v___x_3224_ = lean_box(v_useNewSemantics_3165_);
v___x_3225_ = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(v___x_3225_, 0, v___x_3224_);
lean_inc(v_mvarId_3163_);
v___x_3226_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_3163_, v___x_3225_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = ((lean_object*)(l_Lean_Meta_simpIfTarget___closed__10));
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_a_3227_);
v___x_3230_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3231_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3163_, v_fvarId_3164_, v_a_3223_, v___x_3228_, v___x_3229_, v_useNewSemantics_3165_, v___x_3230_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3244_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3244_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3244_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_fst_3236_; 
v_fst_3236_ = lean_ctor_get(v_a_3232_, 0);
lean_inc(v_fst_3236_);
lean_dec(v_a_3232_);
if (lean_obj_tag(v_fst_3236_) == 1)
{
lean_object* v_val_3237_; lean_object* v_snd_3238_; lean_object* v___x_3240_; 
v_val_3237_ = lean_ctor_get(v_fst_3236_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v_fst_3236_, 1);
v_snd_3238_ = lean_ctor_get(v_val_3237_, 1);
lean_inc(v_snd_3238_);
lean_dec(v_val_3237_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_snd_3238_);
v___x_3240_ = v___x_3234_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_snd_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_dec(v_fst_3236_);
lean_del_object(v___x_3234_);
v___x_3242_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__2, &l_Lean_Meta_simpIfLocalDecl___closed__2_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__2);
v___x_3243_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3242_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
return v___x_3243_;
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_a_3245_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3231_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3231_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_a_3223_);
lean_dec(v_fvarId_3164_);
lean_dec(v_mvarId_3163_);
v_a_3253_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3226_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3226_);
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
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v_fvarId_3164_);
lean_dec(v_mvarId_3163_);
v_a_3261_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3222_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3222_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
else
{
goto v___jp_3171_;
}
v___jp_3171_:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_3166_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
lean_inc(v_mvarId_3163_);
v___x_3174_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(v_mvarId_3163_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v___x_3176_ = 0;
v___x_3177_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_3175_, v___x_3176_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
v___x_3179_ = lean_box(0);
v___x_3180_ = lean_obj_once(&l_Lean_Meta_simpIfTarget___closed__5, &l_Lean_Meta_simpIfTarget___closed__5_once, _init_l_Lean_Meta_simpIfTarget___closed__5);
v___x_3181_ = l_Lean_Meta_simpLocalDecl(v_mvarId_3163_, v_fvarId_3164_, v_a_3173_, v_a_3178_, v___x_3179_, v___x_3176_, v___x_3180_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3194_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_fst_3186_; 
v_fst_3186_ = lean_ctor_get(v_a_3182_, 0);
lean_inc(v_fst_3186_);
lean_dec(v_a_3182_);
if (lean_obj_tag(v_fst_3186_) == 1)
{
lean_object* v_val_3187_; lean_object* v_snd_3188_; lean_object* v___x_3190_; 
v_val_3187_ = lean_ctor_get(v_fst_3186_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v_fst_3186_, 1);
v_snd_3188_ = lean_ctor_get(v_val_3187_, 1);
lean_inc(v_snd_3188_);
lean_dec(v_val_3187_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v_snd_3188_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_snd_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec(v_fst_3186_);
lean_del_object(v___x_3184_);
v___x_3192_ = lean_obj_once(&l_Lean_Meta_simpIfLocalDecl___closed__1, &l_Lean_Meta_simpIfLocalDecl___closed__1_once, _init_l_Lean_Meta_simpIfLocalDecl___closed__1);
v___x_3193_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(v___x_3192_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
return v___x_3193_;
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
v_a_3195_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3181_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3181_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_a_3173_);
lean_dec(v_fvarId_3164_);
lean_dec(v_mvarId_3163_);
v_a_3203_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3174_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3174_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_fvarId_3164_);
lean_dec(v_mvarId_3163_);
v_a_3211_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3172_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3172_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_simpIfLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3163_ = stack[0].m_obj;
lean_object* v_fvarId_3164_ = stack[1].m_obj;
uint8_t v_useNewSemantics_3165_ = stack[2].m_num;
lean_object* v_a_3166_ = stack[3].m_obj;
lean_object* v_a_3167_ = stack[4].m_obj;
lean_object* v_a_3168_ = stack[5].m_obj;
lean_object* v_a_3169_ = stack[6].m_obj;
lean_object* v_res_3269_;
v_res_3269_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3163_, v_fvarId_3164_, v_useNewSemantics_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
stack->m_obj
 = v_res_3269_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl___boxed(lean_object* v_mvarId_3270_, lean_object* v_fvarId_3271_, lean_object* v_useNewSemantics_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
uint8_t v_useNewSemantics_boxed_3278_; lean_object* v_res_3279_; 
v_useNewSemantics_boxed_3278_ = lean_unbox(v_useNewSemantics_3272_);
v_res_3279_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3270_, v_fvarId_3271_, v_useNewSemantics_boxed_3278_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
return v_res_3279_;
}
}
lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* v_x_x3f_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_Meta_saveState___redArg(v___y_3282_, v___y_3284_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3331_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3331_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3331_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v_a_3315_; lean_object* v___x_3318_; 
lean_inc(v___y_3284_);
lean_inc_ref(v___y_3283_);
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3281_);
v___x_3318_ = lean_apply_5(v_x_x3f_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, lean_box(0));
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
if (lean_obj_tag(v_a_3319_) == 0)
{
lean_object* v___x_3320_; 
lean_dec_ref_known(v___x_3318_, 1);
lean_inc(v_a_3287_);
v___x_3320_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3287_, v___y_3282_, v___y_3284_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v___x_3320_, 0);
lean_dec(v_unused_3328_);
v___x_3322_ = v___x_3320_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v___x_3320_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_a_3319_);
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3319_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
else
{
lean_object* v_a_3329_; 
v_a_3329_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3320_, 1);
v_a_3315_ = v_a_3329_;
goto v___jp_3314_;
}
}
else
{
lean_dec_ref_known(v_a_3319_, 1);
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
return v___x_3318_;
}
}
else
{
lean_object* v_a_3330_; 
v_a_3330_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3318_, 1);
v_a_3315_ = v_a_3330_;
goto v___jp_3314_;
}
v___jp_3291_:
{
if (v___y_3293_ == 0)
{
lean_object* v___x_3294_; 
lean_del_object(v___x_3289_);
v___x_3294_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3287_, v___y_3282_, v___y_3284_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; 
v_unused_3302_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3302_);
v___x_3296_ = v___x_3294_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3294_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 1);
lean_ctor_set(v___x_3296_, 0, v___y_3292_);
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___y_3292_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v___y_3292_);
v_a_3303_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3294_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3294_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v___x_3312_; 
lean_dec(v_a_3287_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 1);
lean_ctor_set(v___x_3289_, 0, v___y_3292_);
v___x_3312_ = v___x_3289_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___y_3292_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
v___jp_3314_:
{
uint8_t v___x_3316_; 
v___x_3316_ = l_Lean_Exception_isInterrupt(v_a_3315_);
if (v___x_3316_ == 0)
{
uint8_t v___x_3317_; 
lean_inc_ref(v_a_3315_);
v___x_3317_ = l_Lean_Exception_isRuntime(v_a_3315_);
v___y_3292_ = v_a_3315_;
v___y_3293_ = v___x_3317_;
goto v___jp_3291_;
}
else
{
v___y_3292_ = v_a_3315_;
v___y_3293_ = v___x_3316_;
goto v___jp_3291_;
}
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v_x_x3f_3280_);
v_a_3332_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3286_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3286_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_x3f_3280_ = stack[0].m_obj;
lean_object* v___y_3281_ = stack[1].m_obj;
lean_object* v___y_3282_ = stack[2].m_obj;
lean_object* v___y_3283_ = stack[3].m_obj;
lean_object* v___y_3284_ = stack[4].m_obj;
lean_object* v_res_3340_;
v_res_3340_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
stack->m_obj
 = v_res_3340_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(lean_object* v_x_x3f_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3347_;
}
}
lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* v_00_u03b1_3348_, lean_object* v_x_x3f_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v_x_x3f_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT void l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_x3f_3349_ = stack[1].m_obj;
lean_object* v___y_3350_ = stack[2].m_obj;
lean_object* v___y_3351_ = stack[3].m_obj;
lean_object* v___y_3352_ = stack[4].m_obj;
lean_object* v___y_3353_ = stack[5].m_obj;
lean_object* v_res_3356_;
v_res_3356_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(lean_box(0), v_x_x3f_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
stack->m_obj
 = v_res_3356_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(lean_object* v_00_u03b1_3357_, lean_object* v_x_x3f_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(v_00_u03b1_3357_, v_x_x3f_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
return v_res_3364_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4));
v___x_3371_ = l_Lean_Name_append(v___x_3370_, v___x_3369_);
return v___x_3371_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3));
v___x_3374_ = l_Lean_stringToMessageData(v___x_3373_);
return v___x_3374_;
}
}
static lean_object* _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5));
v___x_3377_ = l_Lean_stringToMessageData(v___x_3376_);
return v___x_3377_;
}
}
lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* v_mvarId_3378_, lean_object* v_hName_x3f_3379_, uint8_t v_useNewSemantics_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3389_; 
lean_inc(v_mvarId_3378_);
v___x_3389_ = l_Lean_MVarId_getType(v_mvarId_3378_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3378_, v_a_3390_, v_hName_x3f_3379_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3489_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3489_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3489_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
if (lean_obj_tag(v_a_3392_) == 1)
{
lean_object* v_val_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3484_; 
lean_del_object(v___x_3394_);
v_val_3396_ = lean_ctor_get(v_a_3392_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_a_3392_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3398_ = v_a_3392_;
v_isShared_3399_ = v_isSharedCheck_3484_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_val_3396_);
lean_dec(v_a_3392_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3484_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_fst_3400_; lean_object* v_snd_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3483_; 
v_fst_3400_ = lean_ctor_get(v_val_3396_, 0);
v_snd_3401_ = lean_ctor_get(v_val_3396_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_val_3396_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3403_ = v_val_3396_;
v_isShared_3404_ = v_isSharedCheck_3483_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snd_3401_);
lean_inc(v_fst_3400_);
lean_dec(v_val_3396_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3483_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_mvarId_3405_; lean_object* v_fvarId_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3482_; 
v_mvarId_3405_ = lean_ctor_get(v_fst_3400_, 0);
v_fvarId_3406_ = lean_ctor_get(v_fst_3400_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_fst_3400_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3408_ = v_fst_3400_;
v_isShared_3409_ = v_isSharedCheck_3482_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_fvarId_3406_);
lean_inc(v_mvarId_3405_);
lean_dec(v_fst_3400_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3482_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
uint8_t v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = 0;
lean_inc(v_mvarId_3405_);
v___x_3411_ = l_Lean_Meta_simpIfTarget(v_mvarId_3405_, v___x_3410_, v_useNewSemantics_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v_mvarId_3413_; lean_object* v_fvarId_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3473_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v_mvarId_3413_ = lean_ctor_get(v_snd_3401_, 0);
v_fvarId_3414_ = lean_ctor_get(v_snd_3401_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_snd_3401_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3416_ = v_snd_3401_;
v_isShared_3417_ = v_isSharedCheck_3473_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_fvarId_3414_);
lean_inc(v_mvarId_3413_);
lean_dec(v_snd_3401_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3473_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; 
lean_inc(v_mvarId_3413_);
v___x_3418_ = l_Lean_Meta_simpIfTarget(v_mvarId_3413_, v___x_3410_, v_useNewSemantics_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3464_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3464_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3464_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
uint8_t v___x_3439_; 
v___x_3439_ = l_Lean_instBEqMVarId_beq(v_mvarId_3405_, v_a_3412_);
lean_dec(v_mvarId_3405_);
if (v___x_3439_ == 0)
{
lean_dec(v_mvarId_3413_);
goto v___jp_3423_;
}
else
{
uint8_t v___x_3440_; 
v___x_3440_ = l_Lean_instBEqMVarId_beq(v_mvarId_3413_, v_a_3419_);
lean_dec(v_mvarId_3413_);
if (v___x_3440_ == 0)
{
goto v___jp_3423_;
}
else
{
lean_object* v_toCold_3441_; lean_object* v_options_3442_; uint8_t v_hasTrace_3443_; 
lean_del_object(v___x_3421_);
lean_del_object(v___x_3416_);
lean_dec(v_fvarId_3414_);
lean_del_object(v___x_3408_);
lean_dec(v_fvarId_3406_);
lean_del_object(v___x_3403_);
lean_del_object(v___x_3398_);
v_toCold_3441_ = lean_ctor_get(v___y_3383_, 0);
v_options_3442_ = lean_ctor_get(v_toCold_3441_, 2);
v_hasTrace_3443_ = lean_ctor_get_uint8(v_options_3442_, sizeof(void*)*1);
if (v_hasTrace_3443_ == 0)
{
lean_dec(v_a_3419_);
lean_dec(v_a_3412_);
goto v___jp_3386_;
}
else
{
lean_object* v_inheritedTraceOptions_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_inheritedTraceOptions_3444_ = lean_ctor_get(v_toCold_3441_, 11);
v___x_3445_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3446_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3447_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3444_, v_options_3442_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_dec(v_a_3419_);
lean_dec(v_a_3412_);
goto v___jp_3386_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3448_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3412_);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_a_3419_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3445_, v___x_3454_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec_ref_known(v___x_3455_, 1);
goto v___jp_3386_;
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
}
v___jp_3423_:
{
lean_object* v___x_3425_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v_fvarId_3406_);
lean_ctor_set(v___x_3416_, 0, v_a_3412_);
v___x_3425_ = v___x_3416_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3412_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_fvarId_3406_);
v___x_3425_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_fvarId_3414_);
lean_ctor_set(v___x_3408_, 0, v_a_3419_);
v___x_3427_ = v___x_3408_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3419_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_fvarId_3414_);
v___x_3427_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3429_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v___x_3427_);
lean_ctor_set(v___x_3403_, 0, v___x_3425_);
v___x_3429_ = v___x_3403_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3429_);
v___x_3431_ = v___x_3398_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3433_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3431_);
v___x_3433_ = v___x_3421_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
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
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3416_);
lean_dec(v_fvarId_3414_);
lean_dec(v_mvarId_3413_);
lean_dec(v_a_3412_);
lean_del_object(v___x_3408_);
lean_dec(v_fvarId_3406_);
lean_dec(v_mvarId_3405_);
lean_del_object(v___x_3403_);
lean_del_object(v___x_3398_);
v_a_3465_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3418_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3418_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_del_object(v___x_3408_);
lean_dec(v_fvarId_3406_);
lean_dec(v_mvarId_3405_);
lean_del_object(v___x_3403_);
lean_dec(v_snd_3401_);
lean_del_object(v___x_3398_);
v_a_3474_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3411_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3411_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
lean_dec(v_a_3392_);
v___x_3485_ = lean_box(0);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v___x_3485_);
v___x_3487_ = v___x_3394_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
return v___x_3391_;
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_hName_x3f_3379_);
lean_dec(v_mvarId_3378_);
v_a_3490_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3389_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3389_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
v___jp_3386_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_splitIfTarget_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3378_ = stack[0].m_obj;
lean_object* v_hName_x3f_3379_ = stack[1].m_obj;
uint8_t v_useNewSemantics_3380_ = stack[2].m_num;
lean_object* v___y_3381_ = stack[3].m_obj;
lean_object* v___y_3382_ = stack[4].m_obj;
lean_object* v___y_3383_ = stack[5].m_obj;
lean_object* v___y_3384_ = stack[6].m_obj;
lean_object* v_res_3498_;
v_res_3498_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3378_, v_hName_x3f_3379_, v_useNewSemantics_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
stack->m_obj
 = v_res_3498_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(lean_object* v_mvarId_3499_, lean_object* v_hName_x3f_3500_, lean_object* v_useNewSemantics_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
uint8_t v_useNewSemantics_boxed_3507_; lean_object* v_res_3508_; 
v_useNewSemantics_boxed_3507_ = lean_unbox(v_useNewSemantics_3501_);
v_res_3508_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(v_mvarId_3499_, v_hName_x3f_3500_, v_useNewSemantics_boxed_3507_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
return v_res_3508_;
}
}
lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* v_mvarId_3509_, lean_object* v_hName_x3f_3510_, uint8_t v_useNewSemantics_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___f_3518_; lean_object* v___x_3519_; 
v___x_3517_ = lean_box(v_useNewSemantics_3511_);
v___f_3518_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3518_, 0, v_mvarId_3509_);
lean_closure_set(v___f_3518_, 1, v_hName_x3f_3510_);
lean_closure_set(v___f_3518_, 2, v___x_3517_);
v___x_3519_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___f_3518_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
return v___x_3519_;
}
}
LEAN_EXPORT void l_Lean_Meta_splitIfTarget_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3509_ = stack[0].m_obj;
lean_object* v_hName_x3f_3510_ = stack[1].m_obj;
uint8_t v_useNewSemantics_3511_ = stack[2].m_num;
lean_object* v_a_3512_ = stack[3].m_obj;
lean_object* v_a_3513_ = stack[4].m_obj;
lean_object* v_a_3514_ = stack[5].m_obj;
lean_object* v_a_3515_ = stack[6].m_obj;
lean_object* v_res_3520_;
v_res_3520_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3509_, v_hName_x3f_3510_, v_useNewSemantics_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
stack->m_obj
 = v_res_3520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___boxed(lean_object* v_mvarId_3521_, lean_object* v_hName_x3f_3522_, lean_object* v_useNewSemantics_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
uint8_t v_useNewSemantics_boxed_3529_; lean_object* v_res_3530_; 
v_useNewSemantics_boxed_3529_ = lean_unbox(v_useNewSemantics_3523_);
v_res_3530_ = l_Lean_Meta_splitIfTarget_x3f(v_mvarId_3521_, v_hName_x3f_3522_, v_useNewSemantics_boxed_3529_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
return v_res_3530_;
}
}
lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* v___x_3531_, lean_object* v_mvarId_3532_, lean_object* v_hName_x3f_3533_, lean_object* v_fvarId_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3543_; 
lean_inc(v___y_3538_);
lean_inc_ref(v___y_3537_);
lean_inc(v___y_3536_);
lean_inc_ref(v___y_3535_);
v___x_3543_ = lean_infer_type(v___x_3531_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(v_mvarId_3532_, v_a_3544_, v_hName_x3f_3533_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3641_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3641_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3641_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
if (lean_obj_tag(v_a_3546_) == 1)
{
lean_object* v_val_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3636_; 
lean_del_object(v___x_3548_);
v_val_3550_ = lean_ctor_get(v_a_3546_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_a_3546_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3552_ = v_a_3546_;
v_isShared_3553_ = v_isSharedCheck_3636_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_val_3550_);
lean_dec(v_a_3546_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3636_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v_fst_3554_; lean_object* v_snd_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3635_; 
v_fst_3554_ = lean_ctor_get(v_val_3550_, 0);
v_snd_3555_ = lean_ctor_get(v_val_3550_, 1);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_val_3550_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3557_ = v_val_3550_;
v_isShared_3558_ = v_isSharedCheck_3635_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_snd_3555_);
lean_inc(v_fst_3554_);
lean_dec(v_val_3550_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3635_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v_mvarId_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3633_; 
v_mvarId_3559_ = lean_ctor_get(v_fst_3554_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_fst_3554_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v_fst_3554_, 1);
lean_dec(v_unused_3634_);
v___x_3561_ = v_fst_3554_;
v_isShared_3562_ = v_isSharedCheck_3633_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_mvarId_3559_);
lean_dec(v_fst_3554_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3633_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
uint8_t v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = 0;
lean_inc(v_fvarId_3534_);
lean_inc(v_mvarId_3559_);
v___x_3564_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3559_, v_fvarId_3534_, v___x_3563_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v_mvarId_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3623_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v_mvarId_3566_ = lean_ctor_get(v_snd_3555_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_snd_3555_);
if (v_isSharedCheck_3623_ == 0)
{
lean_object* v_unused_3624_; 
v_unused_3624_ = lean_ctor_get(v_snd_3555_, 1);
lean_dec(v_unused_3624_);
v___x_3568_ = v_snd_3555_;
v_isShared_3569_ = v_isSharedCheck_3623_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_mvarId_3566_);
lean_dec(v_snd_3555_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3623_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3570_; 
lean_inc(v_mvarId_3566_);
v___x_3570_ = l_Lean_Meta_simpIfLocalDecl(v_mvarId_3566_, v_fvarId_3534_, v___x_3563_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3614_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3614_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3614_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
uint8_t v___x_3585_; 
v___x_3585_ = l_Lean_instBEqMVarId_beq(v_mvarId_3559_, v_a_3565_);
lean_dec(v_mvarId_3559_);
if (v___x_3585_ == 0)
{
lean_del_object(v___x_3568_);
lean_dec(v_mvarId_3566_);
lean_del_object(v___x_3561_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
goto v___jp_3575_;
}
else
{
uint8_t v___x_3586_; 
v___x_3586_ = l_Lean_instBEqMVarId_beq(v_mvarId_3566_, v_a_3571_);
lean_dec(v_mvarId_3566_);
if (v___x_3586_ == 0)
{
lean_del_object(v___x_3568_);
lean_del_object(v___x_3561_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
goto v___jp_3575_;
}
else
{
lean_object* v_toCold_3587_; lean_object* v_options_3588_; uint8_t v_hasTrace_3589_; 
lean_del_object(v___x_3573_);
lean_del_object(v___x_3557_);
lean_del_object(v___x_3552_);
v_toCold_3587_ = lean_ctor_get(v___y_3537_, 0);
v_options_3588_ = lean_ctor_get(v_toCold_3587_, 2);
v_hasTrace_3589_ = lean_ctor_get_uint8(v_options_3588_, sizeof(void*)*1);
if (v_hasTrace_3589_ == 0)
{
lean_dec(v_a_3571_);
lean_del_object(v___x_3568_);
lean_dec(v_a_3565_);
lean_del_object(v___x_3561_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
goto v___jp_3540_;
}
else
{
lean_object* v_inheritedTraceOptions_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v_inheritedTraceOptions_3590_ = lean_ctor_get(v_toCold_3587_, 11);
v___x_3591_ = ((lean_object*)(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1));
v___x_3592_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2);
v___x_3593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3590_, v_options_3588_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_dec(v_a_3571_);
lean_del_object(v___x_3568_);
lean_dec(v_a_3565_);
lean_del_object(v___x_3561_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
goto v___jp_3540_;
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3594_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4);
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_a_3565_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set_tag(v___x_3568_, 7);
lean_ctor_set(v___x_3568_, 1, v___x_3595_);
lean_ctor_set(v___x_3568_, 0, v___x_3594_);
v___x_3597_ = v___x_3568_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3598_ = lean_obj_once(&l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6, &l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once, _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 7);
lean_ctor_set(v___x_3561_, 1, v___x_3598_);
lean_ctor_set(v___x_3561_, 0, v___x_3597_);
v___x_3600_ = v___x_3561_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_a_3571_);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_3591_, v___x_3602_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_dec_ref_known(v___x_3603_, 1);
goto v___jp_3540_;
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
}
}
}
}
v___jp_3575_:
{
lean_object* v___x_3577_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v_a_3571_);
lean_ctor_set(v___x_3557_, 0, v_a_3565_);
v___x_3577_ = v___x_3557_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3565_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_a_3571_);
v___x_3577_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3579_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3577_);
v___x_3579_ = v___x_3552_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3579_);
v___x_3581_ = v___x_3573_;
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
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_del_object(v___x_3568_);
lean_dec(v_mvarId_3566_);
lean_dec(v_a_3565_);
lean_del_object(v___x_3561_);
lean_dec(v_mvarId_3559_);
lean_del_object(v___x_3557_);
lean_del_object(v___x_3552_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
v_a_3615_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3570_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3570_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_del_object(v___x_3561_);
lean_dec(v_mvarId_3559_);
lean_del_object(v___x_3557_);
lean_dec(v_snd_3555_);
lean_del_object(v___x_3552_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v_fvarId_3534_);
v_a_3625_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3564_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3564_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3639_; 
lean_dec(v_a_3546_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v_fvarId_3534_);
v___x_3637_ = lean_box(0);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v___x_3637_);
v___x_3639_ = v___x_3548_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v_fvarId_3534_);
v_a_3642_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3545_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3545_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v_fvarId_3534_);
lean_dec(v_hName_x3f_3533_);
lean_dec(v_mvarId_3532_);
v_a_3650_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3543_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3543_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
v___jp_3540_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
return v___x_3542_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_splitIfLocalDecl_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3531_ = stack[0].m_obj;
lean_object* v_mvarId_3532_ = stack[1].m_obj;
lean_object* v_hName_x3f_3533_ = stack[2].m_obj;
lean_object* v_fvarId_3534_ = stack[3].m_obj;
lean_object* v___y_3535_ = stack[4].m_obj;
lean_object* v___y_3536_ = stack[5].m_obj;
lean_object* v___y_3537_ = stack[6].m_obj;
lean_object* v___y_3538_ = stack[7].m_obj;
lean_object* v_res_3658_;
v_res_3658_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3531_, v_mvarId_3532_, v_hName_x3f_3533_, v_fvarId_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
stack->m_obj
 = v_res_3658_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(lean_object* v___x_3659_, lean_object* v_mvarId_3660_, lean_object* v_hName_x3f_3661_, lean_object* v_fvarId_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(v___x_3659_, v_mvarId_3660_, v_hName_x3f_3661_, v_fvarId_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v_res_3668_;
}
}
lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* v_mvarId_3669_, lean_object* v_fvarId_3670_, lean_object* v_hName_x3f_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___x_3677_; lean_object* v___f_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
lean_inc(v_fvarId_3670_);
v___x_3677_ = l_Lean_mkFVar(v_fvarId_3670_);
lean_inc(v_mvarId_3669_);
v___f_3678_ = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3678_, 0, v___x_3677_);
lean_closure_set(v___f_3678_, 1, v_mvarId_3669_);
lean_closure_set(v___f_3678_, 2, v_hName_x3f_3671_);
lean_closure_set(v___f_3678_, 3, v_fvarId_3670_);
v___x_3679_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3679_, 0, lean_box(0));
lean_closure_set(v___x_3679_, 1, v_mvarId_3669_);
lean_closure_set(v___x_3679_, 2, v___f_3678_);
v___x_3680_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(v___x_3679_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
return v___x_3680_;
}
}
LEAN_EXPORT void l_Lean_Meta_splitIfLocalDecl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3669_ = stack[0].m_obj;
lean_object* v_fvarId_3670_ = stack[1].m_obj;
lean_object* v_hName_x3f_3671_ = stack[2].m_obj;
lean_object* v_a_3672_ = stack[3].m_obj;
lean_object* v_a_3673_ = stack[4].m_obj;
lean_object* v_a_3674_ = stack[5].m_obj;
lean_object* v_a_3675_ = stack[6].m_obj;
lean_object* v_res_3681_;
v_res_3681_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3669_, v_fvarId_3670_, v_hName_x3f_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
stack->m_obj
 = v_res_3681_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___boxed(lean_object* v_mvarId_3682_, lean_object* v_fvarId_3683_, lean_object* v_hName_x3f_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_Meta_splitIfLocalDecl_x3f(v_mvarId_3682_, v_fvarId_3683_, v_hName_x3f_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
return v_res_3690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = lean_unsigned_to_nat(3526097586u);
v___x_3712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3713_ = l_Lean_Name_num___override(v___x_3712_, v___x_3711_);
return v___x_3713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3717_ = l_Lean_Name_str___override(v___x_3716_, v___x_3715_);
return v___x_3717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_));
v___x_3720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3721_ = l_Lean_Name_str___override(v___x_3720_, v___x_3719_);
return v___x_3721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_unsigned_to_nat(2u);
v___x_3723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3724_ = l_Lean_Name_num___override(v___x_3723_, v___x_3722_);
return v___x_3724_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9));
v___x_3727_ = 0;
v___x_3728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
v___x_3729_ = l_Lean_registerTraceClass(v___x_3726_, v___x_3727_, v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3730_;
v_res_3730_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3730_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
return v_res_3732_;
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
