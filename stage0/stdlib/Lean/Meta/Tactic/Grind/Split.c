// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Split
// Imports: public import Lean.Meta.Tactic.Grind.Action public import Lean.Meta.Tactic.Grind.Anchor import Lean.Meta.Tactic.Grind.Intro import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Internalize import Init.Data.List.MapIdx import Init.Grind.Util import Init.Omega
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_casesMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_source(lean_object*);
lean_object* l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Goal_isCongruent(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getHoistedDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_Grind_mkHoistedDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_setIntroBase(lean_object*, uint64_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getProofInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_List_zipIdxTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkHoistedDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_withHoistedDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getGeneration(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSplitStatus_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSplitStatus;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqSplitStatus_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqSplitStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqSplitStatus___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqSplitStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqSplitStatus = (const lean_object*)&l_Lean_Meta_Grind_instBEqSplitStatus___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Grind.SplitStatus.notReady"};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Grind.SplitStatus.resolved"};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5;
static const lean_string_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.Grind.SplitStatus.ready"};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprSplitStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprSplitStatus___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprSplitStatus = (const lean_object*)&l_Lean_Meta_Grind_instReprSplitStatus___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object**);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "cannot perform case-split on "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ", unexpected type"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6_value),LEAN_SCALAR_PTR_LITERAL(26, 217, 152, 239, 89, 139, 148, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "split resolved: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__19_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 59, 213, 47, 128, 196, 59, 0)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "may be irrelevant\na: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nb: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\neq: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\narg_a: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\narg_b: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", gen: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checking: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "em"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2_value),LEAN_SCALAR_PTR_LITERAL(150, 105, 99, 67, 143, 55, 153, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "of_eq_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 180, 29, 33, 135, 171, 75, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "of_eq_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 242, 111, 233, 108, 43, 191, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "or_of_and_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value),LEAN_SCALAR_PTR_LITERAL(64, 20, 245, 101, 69, 170, 96, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor = (const lean_object*)&l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t, uint64_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t, uint64_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 158, 17, 45, 135, 214, 137)}};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_ref__/__"};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(163, 78, 76, 1, 128, 192, 165, 233)}};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_ref_"};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(236, 234, 46, 225, 9, 69, 165, 154)}};
static const lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 82, 43, 49, 91, 105, 112, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value;
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value_aux_3),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value;
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2_value;
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_3),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value;
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4_value;
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_3),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value;
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 96, 222, 221, 183, 249, 85, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 229, 204, 205, 179, 221, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 71, 141, 15, 124, 86, 0, 175)}};
static const lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", generation: "};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0_value;
static const lean_array_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_splitNext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_splitNext___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitNext___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_SplitStatus_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
lean_object* v_numCases_7_; uint8_t v_isRec_8_; uint8_t v_tryPostpone_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_numCases_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_numCases_7_);
v_isRec_8_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*1);
v_tryPostpone_9_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_box(v_isRec_8_);
v___x_11_ = lean_box(v_tryPostpone_9_);
v___x_12_ = lean_apply_3(v_k_6_, v_numCases_7_, v___x_10_, v___x_11_);
return v___x_12_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Grind_SplitStatus_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim___redArg(lean_object* v_t_25_, lean_object* v_resolved_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_25_, v_resolved_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_resolved_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_29_, v_resolved_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim___redArg(lean_object* v_t_33_, lean_object* v_notReady_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_33_, v_notReady_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_notReady_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_37_, v_notReady_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim___redArg(lean_object* v_t_41_, lean_object* v_ready_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_41_, v_ready_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_ready_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_45_, v_ready_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus_default(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqSplitStatus_beq(lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
switch(lean_obj_tag(v_x_51_))
{
case 0:
{
if (lean_obj_tag(v_x_52_) == 0)
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
case 1:
{
if (lean_obj_tag(v_x_52_) == 1)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
default: 
{
if (lean_obj_tag(v_x_52_) == 2)
{
lean_object* v_numCases_57_; uint8_t v_isRec_58_; uint8_t v_tryPostpone_59_; lean_object* v_numCases_60_; uint8_t v_isRec_61_; uint8_t v_tryPostpone_62_; uint8_t v___y_64_; uint8_t v___x_65_; 
v_numCases_57_ = lean_ctor_get(v_x_51_, 0);
v_isRec_58_ = lean_ctor_get_uint8(v_x_51_, sizeof(void*)*1);
v_tryPostpone_59_ = lean_ctor_get_uint8(v_x_51_, sizeof(void*)*1 + 1);
v_numCases_60_ = lean_ctor_get(v_x_52_, 0);
v_isRec_61_ = lean_ctor_get_uint8(v_x_52_, sizeof(void*)*1);
v_tryPostpone_62_ = lean_ctor_get_uint8(v_x_52_, sizeof(void*)*1 + 1);
v___x_65_ = lean_nat_dec_eq(v_numCases_57_, v_numCases_60_);
if (v___x_65_ == 0)
{
return v___x_65_;
}
else
{
if (v_isRec_61_ == 0)
{
if (v_isRec_58_ == 0)
{
v___y_64_ = v___x_65_;
goto v___jp_63_;
}
else
{
return v_isRec_61_;
}
}
else
{
if (v_isRec_58_ == 0)
{
return v_isRec_58_;
}
else
{
v___y_64_ = v_isRec_58_;
goto v___jp_63_;
}
}
}
v___jp_63_:
{
if (v_tryPostpone_62_ == 0)
{
if (v_tryPostpone_59_ == 0)
{
return v___y_64_;
}
else
{
return v_tryPostpone_62_;
}
}
else
{
return v_tryPostpone_59_;
}
}
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_Meta_Grind_instBEqSplitStatus_beq(v_x_67_, v_x_68_);
lean_dec(v_x_68_);
lean_dec(v_x_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(2u);
v___x_80_ = lean_nat_to_int(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr(lean_object* v_x_89_, lean_object* v_prec_90_){
_start:
{
lean_object* v___y_92_; lean_object* v___y_99_; 
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_90_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_99_ = v___x_107_;
goto v___jp_98_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_99_ = v___x_108_;
goto v___jp_98_;
}
}
case 1:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_prec_90_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_92_ = v___x_112_;
goto v___jp_91_;
}
}
default: 
{
lean_object* v_numCases_113_; uint8_t v_isRec_114_; uint8_t v_tryPostpone_115_; lean_object* v___y_117_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_numCases_113_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_numCases_113_);
v_isRec_114_ = lean_ctor_get_uint8(v_x_89_, sizeof(void*)*1);
v_tryPostpone_115_ = lean_ctor_get_uint8(v_x_89_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_89_, 1);
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = lean_nat_dec_le(v___x_133_, v_prec_90_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_117_ = v___x_135_;
goto v___jp_116_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_117_ = v___x_136_;
goto v___jp_116_;
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_118_ = lean_box(1);
v___x_119_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8));
v___x_120_ = l_Nat_reprFast(v_numCases_113_);
v___x_121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_118_);
v___x_124_ = l_Bool_repr___redArg(v_isRec_114_);
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_118_);
v___x_127_ = l_Bool_repr___redArg(v_tryPostpone_115_);
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
lean_inc(v___y_117_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___y_117_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_130_);
v___x_132_ = l_Repr_addAppParen(v___x_131_, v_prec_90_);
return v___x_132_;
}
}
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_90_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_90_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed(lean_object* v_x_137_, lean_object* v_prec_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_Grind_instReprSplitStatus_repr(v_x_137_, v_prec_138_);
lean_dec(v_prec_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(lean_object* v_c_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_153_; 
lean_inc_ref(v_c_142_);
v___x_153_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; uint8_t v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = lean_unbox(v_a_154_);
lean_dec(v_a_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_169_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_169_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_a_157_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; uint8_t v___x_165_; lean_object* v___x_167_; 
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___x_164_ = lean_unbox(v_a_157_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_164_);
v___x_165_ = lean_unbox(v_a_157_);
lean_dec(v_a_157_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1 + 1, v___x_165_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_163_);
v___x_167_ = v___x_159_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_163_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_del_object(v___x_159_);
lean_dec(v_a_157_);
goto v___jp_150_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_156_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_156_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_dec_ref(v_c_142_);
goto v___jp_150_;
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v_c_142_);
v_a_178_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_153_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_153_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg___boxed(lean_object* v_c_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v_c_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus(lean_object* v_c_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v_c_195_, v_a_196_, v_a_200_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___boxed(lean_object* v_c_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus(v_c_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* v_e_221_, lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_234_; 
lean_inc_ref(v_e_221_);
v___x_234_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_221_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; uint8_t v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = lean_unbox(v_a_235_);
lean_dec(v_a_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v_b_223_);
lean_dec_ref(v_a_222_);
v___x_237_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_221_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_251_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_251_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_251_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_251_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; 
v___x_242_ = lean_unbox(v_a_238_);
lean_dec(v_a_238_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_box(1);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_247_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_237_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_237_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec_ref(v_e_221_);
v___x_260_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_222_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; uint8_t v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = lean_unbox(v_a_261_);
lean_dec(v_a_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_276_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_276_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_276_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_276_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_a_264_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_274_; 
v___x_269_ = lean_unsigned_to_nat(2u);
v___x_270_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = lean_unbox(v_a_264_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_271_);
v___x_272_ = lean_unbox(v_a_264_);
lean_dec(v_a_264_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1 + 1, v___x_272_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_270_);
v___x_274_ = v___x_266_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_270_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_del_object(v___x_266_);
lean_dec(v_a_264_);
goto v___jp_231_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_263_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_263_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_dec_ref(v_b_223_);
goto v___jp_231_;
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_b_223_);
v_a_285_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_260_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_260_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_b_223_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_221_);
v_a_293_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_234_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_234_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
v___jp_231_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object* v_e_301_, lean_object* v_a_302_, lean_object* v_b_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_301_, v_a_302_, v_b_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_b_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_312_, v_a_313_, v_b_314_, v_a_315_, v_a_319_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_b_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(v_e_327_, v_a_328_, v_b_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec(v_a_330_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_355_; 
lean_inc_ref(v_e_342_);
v___x_355_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_342_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_417_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_417_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_417_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_417_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; 
v___x_360_ = lean_unbox(v_a_356_);
lean_dec(v_a_356_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
lean_del_object(v___x_358_);
v___x_361_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_342_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_404_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_404_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_404_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_404_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; 
v___x_366_ = lean_unbox(v_a_362_);
lean_dec(v_a_362_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_369_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v___x_367_ = lean_box(1);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_371_; 
lean_del_object(v___x_364_);
v___x_371_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_343_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; uint8_t v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = lean_unbox(v_a_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; lean_object* v___x_385_; 
v___x_380_ = lean_unsigned_to_nat(2u);
v___x_381_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = lean_unbox(v_a_375_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_382_);
v___x_383_ = lean_unbox(v_a_375_);
lean_dec(v_a_375_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1 + 1, v___x_383_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_381_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_381_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_del_object(v___x_377_);
lean_dec(v_a_375_);
goto v___jp_352_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_374_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_374_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_dec_ref(v_b_344_);
goto v___jp_352_;
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_b_344_);
v_a_396_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_371_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_371_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v_a_405_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_361_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_361_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_e_342_);
v___x_413_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_413_);
v___x_415_ = v___x_358_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_e_342_);
v_a_418_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_355_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_355_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
v___jp_352_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_b_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_426_, v_a_427_, v_b_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_437_, v_a_438_, v_b_439_, v_a_440_, v_a_444_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* v_e_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(v_e_452_, v_a_453_, v_b_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec(v_a_455_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
uint8_t v_a_478_; uint8_t v_a_511_; lean_object* v___x_543_; 
lean_inc_ref(v_e_467_);
v___x_543_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_467_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; uint8_t v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_467_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_578_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_578_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_578_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_578_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v___x_552_ = lean_box(1);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v___x_556_; 
lean_del_object(v___x_549_);
lean_inc_ref(v_a_468_);
v___x_556_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; uint8_t v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
if (v___x_558_ == 0)
{
goto v___jp_485_;
}
else
{
lean_object* v___x_559_; 
lean_inc_ref(v_b_469_);
v___x_559_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; uint8_t v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_unbox(v_a_560_);
lean_dec(v_a_560_);
if (v___x_561_ == 0)
{
goto v___jp_485_;
}
else
{
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
goto v___jp_482_;
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_562_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_559_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_570_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_556_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_556_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_579_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_546_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_546_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v_e_467_);
lean_inc_ref(v_a_468_);
v___x_587_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; uint8_t v___x_589_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = lean_unbox(v_a_588_);
lean_dec(v_a_588_);
if (v___x_589_ == 0)
{
goto v___jp_518_;
}
else
{
lean_object* v___x_590_; 
lean_inc_ref(v_b_469_);
v___x_590_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; uint8_t v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_unbox(v_a_591_);
lean_dec(v_a_591_);
if (v___x_592_ == 0)
{
goto v___jp_518_;
}
else
{
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
goto v___jp_515_;
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_593_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_590_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_590_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_601_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_587_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_587_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
lean_dec_ref(v_e_467_);
v_a_609_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_543_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_543_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v_a_478_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1 + 1, v_a_478_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
v___jp_482_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
v___jp_485_:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; uint8_t v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = lean_unbox(v_a_487_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; 
lean_dec_ref(v_b_469_);
v___x_489_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
v_a_478_ = v___x_489_;
goto v___jp_477_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_a_487_);
v___x_490_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox(v_a_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
v_a_478_ = v___x_493_;
goto v___jp_477_;
}
else
{
lean_dec(v_a_491_);
goto v___jp_482_;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_490_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_b_469_);
v_a_502_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_486_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_486_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(2u);
v___x_513_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*1, v_a_511_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*1 + 1, v_a_511_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
v___jp_515_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; uint8_t v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_unbox(v_a_520_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; 
lean_dec_ref(v_b_469_);
v___x_522_ = lean_unbox(v_a_520_);
lean_dec(v_a_520_);
v_a_511_ = v___x_522_;
goto v___jp_510_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v_a_520_);
v___x_523_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; uint8_t v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_unbox(v_a_524_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = lean_unbox(v_a_524_);
lean_dec(v_a_524_);
v_a_511_ = v___x_526_;
goto v___jp_510_;
}
else
{
lean_dec(v_a_524_);
goto v___jp_515_;
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_523_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_523_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_b_469_);
v_a_535_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_519_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_519_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_617_, v_a_618_, v_b_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_628_, v_a_629_, v_b_630_, v_a_631_, v_a_635_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* v_e_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(v_e_643_, v_a_644_, v_b_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object* v_c_658_, uint8_t v___x_659_, uint8_t v_d_660_, lean_object* v_a_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
if (v_d_660_ == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_st_ref_get(v___y_663_);
v___x_675_ = l_Lean_Expr_isApp(v_a_661_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_674_);
lean_dec_ref(v_a_661_);
lean_dec_ref(v_c_658_);
v___x_676_ = lean_box(v_d_660_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
else
{
uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Meta_Grind_Goal_isCongruent(v___x_674_, v_c_658_, v_a_661_);
lean_dec(v___x_674_);
v___x_679_ = lean_box(v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_a_661_);
lean_dec_ref(v_c_658_);
v___x_681_ = lean_box(v___x_659_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* v_c_683_, lean_object* v___x_684_, lean_object* v_d_685_, lean_object* v_a_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_7896__boxed_699_; uint8_t v_d_boxed_700_; lean_object* v_res_701_; 
v___x_7896__boxed_699_ = lean_unbox(v___x_684_);
v_d_boxed_700_ = lean_unbox(v_d_685_);
v_res_701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_683_, v___x_7896__boxed_699_, v_d_boxed_700_, v_a_686_, v_x_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(lean_object* v_f_702_, lean_object* v_keys_703_, lean_object* v_vals_704_, lean_object* v_i_705_, lean_object* v_acc_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_get_size(v_keys_703_);
v___x_719_ = lean_nat_dec_lt(v_i_705_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_i_705_);
lean_dec_ref(v_f_702_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_acc_706_);
return v___x_720_;
}
else
{
lean_object* v_k_721_; lean_object* v_v_722_; lean_object* v___x_723_; 
v_k_721_ = lean_array_fget_borrowed(v_keys_703_, v_i_705_);
v_v_722_ = lean_array_fget_borrowed(v_vals_704_, v_i_705_);
lean_inc_ref(v_f_702_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc(v___y_707_);
lean_inc(v_v_722_);
lean_inc(v_k_721_);
v___x_723_ = lean_apply_14(v_f_702_, v_acc_706_, v_k_721_, v_v_722_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, lean_box(0));
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_i_705_, v___x_725_);
lean_dec(v_i_705_);
v_i_705_ = v___x_726_;
v_acc_706_ = v_a_724_;
goto _start;
}
else
{
lean_dec(v_i_705_);
lean_dec_ref(v_f_702_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_728_, lean_object* v_keys_729_, lean_object* v_vals_730_, lean_object* v_i_731_, lean_object* v_acc_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_728_, v_keys_729_, v_vals_730_, v_i_731_, v_acc_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v_vals_730_);
lean_dec_ref(v_keys_729_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* v_f_745_, lean_object* v_as_746_, size_t v_i_747_, size_t v_stop_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_a_762_; lean_object* v___y_767_; uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_eq(v_i_747_, v_stop_748_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_array_uget_borrowed(v_as_746_, v_i_747_);
switch(lean_obj_tag(v___x_770_))
{
case 0:
{
lean_object* v_key_771_; lean_object* v_val_772_; lean_object* v___x_773_; 
v_key_771_ = lean_ctor_get(v___x_770_, 0);
v_val_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc_ref(v_f_745_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc(v___y_750_);
lean_inc(v_val_772_);
lean_inc(v_key_771_);
v___x_773_ = lean_apply_14(v_f_745_, v_b_749_, v_key_771_, v_val_772_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, lean_box(0));
v___y_767_ = v___x_773_;
goto v___jp_766_;
}
case 1:
{
lean_object* v_node_774_; lean_object* v___x_775_; 
v_node_774_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_node_774_);
lean_inc_ref(v_f_745_);
v___x_775_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_745_, v_node_774_, v_b_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_767_ = v___x_775_;
goto v___jp_766_;
}
default: 
{
v_a_762_ = v_b_749_;
goto v___jp_761_;
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec_ref(v_f_745_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_b_749_);
return v___x_776_;
}
v___jp_761_:
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_747_, v___x_763_);
v_i_747_ = v___x_764_;
v_b_749_ = v_a_762_;
goto _start;
}
v___jp_766_:
{
if (lean_obj_tag(v___y_767_) == 0)
{
lean_object* v_a_768_; 
v_a_768_ = lean_ctor_get(v___y_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___y_767_, 1);
v_a_762_ = v_a_768_;
goto v___jp_761_;
}
else
{
lean_dec_ref(v_f_745_);
return v___y_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* v_f_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v_es_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_804_; 
v_es_791_ = lean_ctor_get(v_x_778_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_804_ == 0)
{
v___x_793_ = v_x_778_;
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_es_791_);
lean_dec(v_x_778_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v_es_791_);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_es_791_);
lean_dec_ref(v_f_777_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_x_779_);
v___x_799_ = v___x_793_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_x_779_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_793_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_796_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_777_, v_es_791_, v___x_801_, v___x_802_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_es_791_);
return v___x_803_;
}
}
}
else
{
lean_object* v_ks_805_; lean_object* v_vs_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_ks_805_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_ks_805_);
v_vs_806_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_vs_806_);
lean_dec_ref_known(v_x_778_, 2);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_777_, v_ks_805_, v_vs_806_, v___x_807_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_vs_806_);
lean_dec_ref(v_ks_805_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_809_, v_x_810_, v_x_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_824_, lean_object* v_as_825_, lean_object* v_i_826_, lean_object* v_stop_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
size_t v_i_boxed_840_; size_t v_stop_boxed_841_; lean_object* v_res_842_; 
v_i_boxed_840_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_stop_boxed_841_ = lean_unbox_usize(v_stop_827_);
lean_dec(v_stop_827_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_824_, v_as_825_, v_i_boxed_840_, v_stop_boxed_841_, v_b_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v_as_825_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* v_c_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Lean_Expr_isApp(v_c_843_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_c_843_);
v___x_856_ = lean_box(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v_toGoalState_861_; lean_object* v_split_862_; lean_object* v_resolved_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_858_ = lean_box(v___x_855_);
v___f_859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 16, 2);
lean_closure_set(v___f_859_, 0, v_c_843_);
lean_closure_set(v___f_859_, 1, v___x_858_);
v___x_860_ = lean_st_ref_get(v_a_844_);
v_toGoalState_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_toGoalState_861_);
lean_dec(v___x_860_);
v_split_862_ = lean_ctor_get(v_toGoalState_861_, 15);
lean_inc_ref(v_split_862_);
lean_dec_ref(v_toGoalState_861_);
v_resolved_863_ = lean_ctor_get(v_split_862_, 2);
lean_inc_ref(v_resolved_863_);
lean_dec_ref(v_split_862_);
v___x_864_ = 0;
v___x_865_ = lean_box(v___x_864_);
v___x_866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v___f_859_, v_resolved_863_, v___x_865_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object* v_c_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec(v_a_868_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* v_map_880_, lean_object* v_f_881_, lean_object* v_init_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_881_, v_map_880_, v_init_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* v_map_895_, lean_object* v_f_896_, lean_object* v_init_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_895_, v_f_896_, v_init_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* v_00_u03c3_910_, lean_object* v_00_u03b2_911_, lean_object* v_map_912_, lean_object* v_f_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_913_, v_map_912_, v_init_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* v_00_u03c3_927_, lean_object* v_00_u03b2_928_, lean_object* v_map_929_, lean_object* v_f_930_, lean_object* v_init_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(v_00_u03c3_927_, v_00_u03b2_928_, v_map_929_, v_f_930_, v_init_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec(v___y_932_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* v_00_u03c3_944_, lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_f_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_947_, v_x_948_, v_x_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_962_ = _args[0];
lean_object* v_00_u03b1_963_ = _args[1];
lean_object* v_00_u03b2_964_ = _args[2];
lean_object* v_f_965_ = _args[3];
lean_object* v_x_966_ = _args[4];
lean_object* v_x_967_ = _args[5];
lean_object* v___y_968_ = _args[6];
lean_object* v___y_969_ = _args[7];
lean_object* v___y_970_ = _args[8];
lean_object* v___y_971_ = _args[9];
lean_object* v___y_972_ = _args[10];
lean_object* v___y_973_ = _args[11];
lean_object* v___y_974_ = _args[12];
lean_object* v___y_975_ = _args[13];
lean_object* v___y_976_ = _args[14];
lean_object* v___y_977_ = _args[15];
lean_object* v___y_978_ = _args[16];
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(v_00_u03c3_962_, v_00_u03b1_963_, v_00_u03b2_964_, v_f_965_, v_x_966_, v_x_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_00_u03c3_982_, lean_object* v_f_983_, lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_983_, v_as_984_, v_i_985_, v_stop_986_, v_b_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_1000_ = _args[0];
lean_object* v_00_u03b2_1001_ = _args[1];
lean_object* v_00_u03c3_1002_ = _args[2];
lean_object* v_f_1003_ = _args[3];
lean_object* v_as_1004_ = _args[4];
lean_object* v_i_1005_ = _args[5];
lean_object* v_stop_1006_ = _args[6];
lean_object* v_b_1007_ = _args[7];
lean_object* v___y_1008_ = _args[8];
lean_object* v___y_1009_ = _args[9];
lean_object* v___y_1010_ = _args[10];
lean_object* v___y_1011_ = _args[11];
lean_object* v___y_1012_ = _args[12];
lean_object* v___y_1013_ = _args[13];
lean_object* v___y_1014_ = _args[14];
lean_object* v___y_1015_ = _args[15];
lean_object* v___y_1016_ = _args[16];
lean_object* v___y_1017_ = _args[17];
lean_object* v___y_1018_ = _args[18];
_start:
{
size_t v_i_boxed_1019_; size_t v_stop_boxed_1020_; lean_object* v_res_1021_; 
v_i_boxed_1019_ = lean_unbox_usize(v_i_1005_);
lean_dec(v_i_1005_);
v_stop_boxed_1020_ = lean_unbox_usize(v_stop_1006_);
lean_dec(v_stop_1006_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(v_00_u03b1_1000_, v_00_u03b2_1001_, v_00_u03c3_1002_, v_f_1003_, v_as_1004_, v_i_boxed_1019_, v_stop_boxed_1020_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v_as_1004_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_1022_, lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_f_1025_, lean_object* v_keys_1026_, lean_object* v_vals_1027_, lean_object* v_heq_1028_, lean_object* v_i_1029_, lean_object* v_acc_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_1025_, v_keys_1026_, v_vals_1027_, v_i_1029_, v_acc_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_1043_ = _args[0];
lean_object* v_00_u03b1_1044_ = _args[1];
lean_object* v_00_u03b2_1045_ = _args[2];
lean_object* v_f_1046_ = _args[3];
lean_object* v_keys_1047_ = _args[4];
lean_object* v_vals_1048_ = _args[5];
lean_object* v_heq_1049_ = _args[6];
lean_object* v_i_1050_ = _args[7];
lean_object* v_acc_1051_ = _args[8];
lean_object* v___y_1052_ = _args[9];
lean_object* v___y_1053_ = _args[10];
lean_object* v___y_1054_ = _args[11];
lean_object* v___y_1055_ = _args[12];
lean_object* v___y_1056_ = _args[13];
lean_object* v___y_1057_ = _args[14];
lean_object* v___y_1058_ = _args[15];
lean_object* v___y_1059_ = _args[16];
lean_object* v___y_1060_ = _args[17];
lean_object* v___y_1061_ = _args[18];
lean_object* v___y_1062_ = _args[19];
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(v_00_u03c3_1043_, v_00_u03b1_1044_, v_00_u03b2_1045_, v_f_1046_, v_keys_1047_, v_vals_1048_, v_heq_1049_, v_i_1050_, v_acc_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v_vals_1048_);
lean_dec_ref(v_keys_1047_);
return v_res_1063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
lean_ctor_set(v___x_1069_, 3, v___x_1068_);
lean_ctor_set(v___x_1069_, 4, v___x_1067_);
lean_ctor_set(v___x_1069_, 5, v___x_1067_);
lean_ctor_set(v___x_1069_, 6, v___x_1067_);
lean_ctor_set(v___x_1069_, 7, v___x_1067_);
lean_ctor_set(v___x_1069_, 8, v___x_1067_);
lean_ctor_set(v___x_1069_, 9, v___x_1067_);
lean_ctor_set(v___x_1069_, 10, v___x_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_unsigned_to_nat(32u);
v___x_1071_ = lean_mk_empty_array_with_capacity(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1073_ = ((size_t)5ULL);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_unsigned_to_nat(32u);
v___x_1076_ = lean_mk_empty_array_with_capacity(v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1078_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1076_);
lean_ctor_set(v___x_1078_, 2, v___x_1074_);
lean_ctor_set(v___x_1078_, 3, v___x_1074_);
lean_ctor_set_usize(v___x_1078_, 4, v___x_1073_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = lean_box(1);
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
lean_ctor_set(v___x_1082_, 2, v___x_1079_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26));
v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1116_, lean_object* v_declHint_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_env_1122_; uint8_t v___x_1123_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_st_ref_get(v___y_1118_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_Name_isAnonymous(v_declHint_1117_);
if (v___x_1123_ == 0)
{
uint8_t v_isExporting_1124_; 
v_isExporting_1124_ = lean_ctor_get_uint8(v_env_1122_, sizeof(void*)*13);
if (v_isExporting_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1117_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_msg_1116_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
lean_inc_ref(v_env_1122_);
v___x_1126_ = l_Lean_Environment_setExporting(v_env_1122_, v___x_1123_);
lean_inc(v_declHint_1117_);
lean_inc_ref(v___x_1126_);
v___x_1127_ = l_Lean_Environment_contains(v___x_1126_, v_declHint_1117_, v_isExporting_1124_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1117_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_msg_1116_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_c_1134_; lean_object* v___x_1135_; 
v___x_1129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1131_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1126_);
v___x_1132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1126_);
lean_ctor_set(v___x_1132_, 1, v___x_1129_);
lean_ctor_set(v___x_1132_, 2, v___x_1130_);
lean_ctor_set(v___x_1132_, 3, v___x_1131_);
lean_inc(v_declHint_1117_);
v___x_1133_ = l_Lean_MessageData_ofConstName(v_declHint_1117_, v___x_1123_);
v_c_1134_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1134_, 0, v___x_1132_);
lean_ctor_set(v_c_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1126_, v_declHint_1117_);
lean_dec_ref(v___x_1126_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1117_);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_c_1134_);
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_note(v___x_1139_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_msg_1116_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1196_; 
v_val_1143_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1145_ = v___x_1135_;
v_isShared_1146_ = v_isSharedCheck_1196_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___x_1135_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1196_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v_modules_1148_; lean_object* v_moduleNames_1149_; lean_object* v_mod_1150_; uint8_t v___x_1165_; 
v___x_1147_ = l_Lean_Environment_header(v_env_1122_);
lean_dec_ref(v_env_1122_);
v_modules_1148_ = lean_ctor_get(v___x_1147_, 3);
lean_inc_ref(v_modules_1148_);
v_moduleNames_1149_ = lean_ctor_get(v___x_1147_, 4);
lean_inc_ref(v_moduleNames_1149_);
lean_dec_ref(v___x_1147_);
v_mod_1150_ = lean_array_get(v___x_1120_, v_moduleNames_1149_, v_val_1143_);
lean_dec_ref(v_moduleNames_1149_);
v___x_1165_ = l_Lean_isPrivateName(v_declHint_1117_);
lean_dec(v_declHint_1117_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_array_get_size(v_modules_1148_);
v___x_1167_ = lean_nat_dec_lt(v_val_1143_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec_ref(v_modules_1148_);
lean_dec(v_val_1143_);
goto v___jp_1151_;
}
else
{
lean_object* v___x_1168_; lean_object* v_toImport_1169_; uint8_t v_isExported_1170_; 
v___x_1168_ = lean_array_fget(v_modules_1148_, v_val_1143_);
lean_dec(v_val_1143_);
lean_dec_ref(v_modules_1148_);
v_toImport_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_toImport_1169_);
lean_dec(v___x_1168_);
v_isExported_1170_ = lean_ctor_get_uint8(v_toImport_1169_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1169_);
if (v_isExported_1170_ == 0)
{
goto v___jp_1151_;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_del_object(v___x_1145_);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_c_1134_);
v___x_1173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_MessageData_ofName(v_mod_1150_);
lean_inc_ref(v___x_1175_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1175_);
v___x_1180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Lean_MessageData_note(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_msg_1116_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v_modules_1148_);
lean_del_object(v___x_1145_);
lean_dec(v_val_1143_);
v___x_1185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_c_1134_);
v___x_1187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_MessageData_ofName(v_mod_1150_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_MessageData_note(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_msg_1116_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
v___jp_1151_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_c_1134_);
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofName(v_mod_1150_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_note(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_msg_1116_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1161_);
v___x_1163_ = v___x_1145_;
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
}
}
}
}
else
{
lean_object* v___x_1197_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1117_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_msg_1116_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1198_, lean_object* v_declHint_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1198_, v_declHint_1199_, v___y_1200_);
lean_dec(v___y_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1203_, lean_object* v_declHint_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1226_; 
v___x_1216_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1203_, v_declHint_1204_, v___y_1214_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1221_ = l_Lean_unknownIdentifierMessageTag;
v___x_1222_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1217_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1222_);
v___x_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1227_, lean_object* v_declHint_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1227_, v_declHint_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec(v___y_1229_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v_env_1248_; uint8_t v___x_1249_; lean_object* v_env_1250_; lean_object* v___x_1251_; lean_object* v_toCold_1252_; lean_object* v_mctx_1253_; lean_object* v_lctx_1254_; lean_object* v_options_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1247_ = lean_st_ref_get(v___y_1245_);
v_env_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc_ref(v_env_1248_);
lean_dec(v___x_1247_);
v___x_1249_ = 0;
v_env_1250_ = l_Lean_Environment_setRecordingDeps(v_env_1248_, v___x_1249_);
v___x_1251_ = lean_st_ref_get(v___y_1243_);
v_toCold_1252_ = lean_ctor_get(v___y_1244_, 0);
v_mctx_1253_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_ref(v_mctx_1253_);
lean_dec(v___x_1251_);
v_lctx_1254_ = lean_ctor_get(v___y_1242_, 2);
v_options_1255_ = lean_ctor_get(v_toCold_1252_, 2);
lean_inc_ref(v_options_1255_);
lean_inc_ref(v_lctx_1254_);
v___x_1256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1256_, 0, v_env_1250_);
lean_ctor_set(v___x_1256_, 1, v_mctx_1253_);
lean_ctor_set(v___x_1256_, 2, v_lctx_1254_);
lean_ctor_set(v___x_1256_, 3, v_options_1255_);
v___x_1257_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_msgData_1241_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_ref_1272_; lean_object* v___x_1273_; lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1282_; 
v_ref_1272_ = lean_ctor_get(v___y_1269_, 2);
v___x_1273_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
lean_inc(v_ref_1272_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_ref_1272_);
lean_ctor_set(v___x_1278_, 1, v_a_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 1);
lean_ctor_set(v___x_1276_, 0, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1290_, lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_toCold_1303_; lean_object* v_currRecDepth_1304_; lean_object* v_ref_1305_; uint16_t v_optionFlags_1306_; uint8_t v_suppressElabErrors_1307_; uint8_t v_checkDeprecated_1308_; uint8_t v_isRecordingDeps_1309_; lean_object* v_ref_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_toCold_1303_ = lean_ctor_get(v___y_1300_, 0);
v_currRecDepth_1304_ = lean_ctor_get(v___y_1300_, 1);
v_ref_1305_ = lean_ctor_get(v___y_1300_, 2);
v_optionFlags_1306_ = lean_ctor_get_uint16(v___y_1300_, sizeof(void*)*3);
v_suppressElabErrors_1307_ = lean_ctor_get_uint8(v___y_1300_, sizeof(void*)*3 + 2);
v_checkDeprecated_1308_ = lean_ctor_get_uint8(v___y_1300_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1309_ = lean_ctor_get_uint8(v___y_1300_, sizeof(void*)*3 + 4);
v_ref_1310_ = l_Lean_replaceRef(v_ref_1290_, v_ref_1305_);
lean_inc(v_currRecDepth_1304_);
lean_inc_ref(v_toCold_1303_);
v___x_1311_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1311_, 0, v_toCold_1303_);
lean_ctor_set(v___x_1311_, 1, v_currRecDepth_1304_);
lean_ctor_set(v___x_1311_, 2, v_ref_1310_);
lean_ctor_set_uint16(v___x_1311_, sizeof(void*)*3, v_optionFlags_1306_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*3 + 2, v_suppressElabErrors_1307_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*3 + 3, v_checkDeprecated_1308_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*3 + 4, v_isRecordingDeps_1309_);
v___x_1312_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1291_, v___y_1298_, v___y_1299_, v___x_1311_, v___y_1301_);
lean_dec_ref_known(v___x_1311_, 3);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1313_, lean_object* v_msg_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1313_, v_msg_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v_ref_1313_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1327_, lean_object* v_msg_1328_, lean_object* v_declHint_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v_a_1342_; lean_object* v___x_1343_; 
v___x_1341_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1328_, v_declHint_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1327_, v_a_1342_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1344_, lean_object* v_msg_1345_, lean_object* v_declHint_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1344_, v_msg_1345_, v_declHint_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec(v_ref_1344_);
return v_res_1358_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1365_, lean_object* v_constName_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1378_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1379_ = 0;
lean_inc(v_constName_1366_);
v___x_1380_ = l_Lean_MessageData_ofConstName(v_constName_1366_, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1378_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1365_, v___x_1383_, v_constName_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1385_, lean_object* v_constName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1385_, v_constName_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec(v_ref_1385_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_ref_1411_; lean_object* v___x_1412_; 
v_ref_1411_ = lean_ctor_get(v___y_1408_, 2);
v___x_1412_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1411_, v_constName_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v_env_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = lean_st_ref_get(v___y_1436_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = 0;
lean_inc(v_constName_1426_);
v___x_1441_ = l_Lean_Environment_find_x3f(v_env_1439_, v_constName_1426_, v___x_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1442_;
}
else
{
lean_object* v_val_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_constName_1426_);
v_val_1443_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1441_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_val_1443_);
lean_dec(v___x_1441_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 0);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec(v___y_1452_);
return v_res_1463_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1464_; double v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_float_of_nat(v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_ref_1476_; lean_object* v___x_1477_; lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1523_; 
v_ref_1476_ = lean_ctor_get(v___y_1473_, 2);
v___x_1477_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1523_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1523_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v_traceState_1483_; lean_object* v_env_1484_; lean_object* v_nextMacroScope_1485_; lean_object* v_ngen_1486_; lean_object* v_auxDeclNGen_1487_; lean_object* v_cache_1488_; lean_object* v_recordedDeps_1489_; lean_object* v_messages_1490_; lean_object* v_infoState_1491_; lean_object* v_snapshotTasks_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1522_; 
v___x_1482_ = lean_st_ref_take(v___y_1474_);
v_traceState_1483_ = lean_ctor_get(v___x_1482_, 4);
v_env_1484_ = lean_ctor_get(v___x_1482_, 0);
v_nextMacroScope_1485_ = lean_ctor_get(v___x_1482_, 1);
v_ngen_1486_ = lean_ctor_get(v___x_1482_, 2);
v_auxDeclNGen_1487_ = lean_ctor_get(v___x_1482_, 3);
v_cache_1488_ = lean_ctor_get(v___x_1482_, 5);
v_recordedDeps_1489_ = lean_ctor_get(v___x_1482_, 6);
v_messages_1490_ = lean_ctor_get(v___x_1482_, 7);
v_infoState_1491_ = lean_ctor_get(v___x_1482_, 8);
v_snapshotTasks_1492_ = lean_ctor_get(v___x_1482_, 9);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1494_ = v___x_1482_;
v_isShared_1495_ = v_isSharedCheck_1522_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snapshotTasks_1492_);
lean_inc(v_infoState_1491_);
lean_inc(v_messages_1490_);
lean_inc(v_recordedDeps_1489_);
lean_inc(v_cache_1488_);
lean_inc(v_traceState_1483_);
lean_inc(v_auxDeclNGen_1487_);
lean_inc(v_ngen_1486_);
lean_inc(v_nextMacroScope_1485_);
lean_inc(v_env_1484_);
lean_dec(v___x_1482_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1522_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint64_t v_tid_1496_; lean_object* v_traces_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1521_; 
v_tid_1496_ = lean_ctor_get_uint64(v_traceState_1483_, sizeof(void*)*1);
v_traces_1497_ = lean_ctor_get(v_traceState_1483_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_traceState_1483_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1499_ = v_traceState_1483_;
v_isShared_1500_ = v_isSharedCheck_1521_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_traces_1497_);
lean_dec(v_traceState_1483_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1521_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; double v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1504_ = 0;
v___x_1505_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1506_, 0, v_cls_1469_);
lean_ctor_set(v___x_1506_, 1, v___x_1502_);
lean_ctor_set(v___x_1506_, 2, v___x_1505_);
lean_ctor_set_float(v___x_1506_, sizeof(void*)*3, v___x_1503_);
lean_ctor_set_float(v___x_1506_, sizeof(void*)*3 + 8, v___x_1503_);
lean_ctor_set_uint8(v___x_1506_, sizeof(void*)*3 + 16, v___x_1504_);
v___x_1507_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1508_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v_a_1478_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_inc(v_ref_1476_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_ref_1476_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = l_Lean_PersistentArray_push___redArg(v_traces_1497_, v___x_1509_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1510_);
v___x_1512_ = v___x_1499_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1510_);
lean_ctor_set_uint64(v_reuseFailAlloc_1520_, sizeof(void*)*1, v_tid_1496_);
v___x_1512_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 4, v___x_1512_);
v___x_1514_ = v___x_1494_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_env_1484_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_nextMacroScope_1485_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_ngen_1486_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_auxDeclNGen_1487_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1519_, 5, v_cache_1488_);
lean_ctor_set(v_reuseFailAlloc_1519_, 6, v_recordedDeps_1489_);
lean_ctor_set(v_reuseFailAlloc_1519_, 7, v_messages_1490_);
lean_ctor_set(v_reuseFailAlloc_1519_, 8, v_infoState_1491_);
lean_ctor_set(v_reuseFailAlloc_1519_, 9, v_snapshotTasks_1492_);
v___x_1514_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1515_ = lean_st_ref_put(v___y_1474_, v___x_1514_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1501_);
v___x_1517_ = v___x_1480_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1501_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1524_, lean_object* v_msg_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1524_, v_msg_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1550_ = l_Lean_Name_append(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___x_1827_; 
lean_inc_ref(v_e_1566_);
v___x_1827_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1566_, v_a_1574_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1859_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1859_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1859_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = l_Lean_Expr_cleanupAnnotations(v_a_1828_);
lean_dec(v_a_1828_);
v___x_1833_ = l_Lean_Expr_isApp(v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v___x_1832_);
lean_del_object(v___x_1830_);
v___y_1707_ = v_a_1567_;
v___y_1708_ = v_a_1568_;
v___y_1709_ = v_a_1569_;
v___y_1710_ = v_a_1570_;
v___y_1711_ = v_a_1571_;
v___y_1712_ = v_a_1572_;
v___y_1713_ = v_a_1573_;
v___y_1714_ = v_a_1574_;
v___y_1715_ = v_a_1575_;
v___y_1716_ = v_a_1576_;
goto v___jp_1706_;
}
else
{
lean_object* v_arg_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_arg_1834_ = lean_ctor_get(v___x_1832_, 1);
lean_inc_ref(v_arg_1834_);
v___x_1835_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1837_ = l_Lean_Expr_isConstOf(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Expr_isApp(v___x_1835_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_arg_1834_);
lean_del_object(v___x_1830_);
v___y_1707_ = v_a_1567_;
v___y_1708_ = v_a_1568_;
v___y_1709_ = v_a_1569_;
v___y_1710_ = v_a_1570_;
v___y_1711_ = v_a_1571_;
v___y_1712_ = v_a_1572_;
v___y_1713_ = v_a_1573_;
v___y_1714_ = v_a_1574_;
v___y_1715_ = v_a_1575_;
v___y_1716_ = v_a_1576_;
goto v___jp_1706_;
}
else
{
lean_object* v_arg_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_arg_1839_ = lean_ctor_get(v___x_1835_, 1);
lean_inc_ref(v_arg_1839_);
v___x_1840_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1842_ = l_Lean_Expr_isConstOf(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1844_ = l_Lean_Expr_isConstOf(v___x_1840_, v___x_1843_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_isApp(v___x_1840_);
if (v___x_1845_ == 0)
{
lean_dec_ref(v___x_1840_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1834_);
lean_del_object(v___x_1830_);
v___y_1707_ = v_a_1567_;
v___y_1708_ = v_a_1568_;
v___y_1709_ = v_a_1569_;
v___y_1710_ = v_a_1570_;
v___y_1711_ = v_a_1571_;
v___y_1712_ = v_a_1572_;
v___y_1713_ = v_a_1573_;
v___y_1714_ = v_a_1574_;
v___y_1715_ = v_a_1575_;
v___y_1716_ = v_a_1576_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1840_);
lean_dec_ref(v___x_1840_);
v___x_1847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20));
v___x_1848_ = l_Lean_Expr_isConstOf(v___x_1846_, v___x_1847_);
lean_dec_ref(v___x_1846_);
if (v___x_1848_ == 0)
{
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1834_);
lean_del_object(v___x_1830_);
v___y_1707_ = v_a_1567_;
v___y_1708_ = v_a_1568_;
v___y_1709_ = v_a_1569_;
v___y_1710_ = v_a_1570_;
v___y_1711_ = v_a_1571_;
v___y_1712_ = v_a_1572_;
v___y_1713_ = v_a_1573_;
v___y_1714_ = v_a_1574_;
v___y_1715_ = v_a_1575_;
v___y_1716_ = v_a_1576_;
goto v___jp_1706_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1566_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1834_);
lean_dec_ref(v_e_1566_);
v___x_1850_ = lean_unsigned_to_nat(2u);
v___x_1851_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*1, v___x_1849_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*1 + 1, v___x_1849_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1851_);
v___x_1853_ = v___x_1830_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v___x_1855_; 
lean_del_object(v___x_1830_);
v___x_1855_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1566_, v_arg_1839_, v_arg_1834_, v_a_1567_, v_a_1571_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1855_;
}
}
}
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1840_);
lean_del_object(v___x_1830_);
v___x_1856_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1566_, v_arg_1839_, v_arg_1834_, v_a_1567_, v_a_1571_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1856_;
}
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v___x_1840_);
lean_del_object(v___x_1830_);
v___x_1857_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1566_, v_arg_1839_, v_arg_1834_, v_a_1567_, v_a_1571_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1857_;
}
}
}
else
{
lean_object* v___x_1858_; 
lean_dec_ref(v___x_1835_);
lean_del_object(v___x_1830_);
lean_dec_ref(v_e_1566_);
v___x_1858_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v_arg_1834_, v_a_1567_, v_a_1571_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_e_1566_);
v_a_1860_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1827_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1827_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
v___jp_1581_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
v___jp_1584_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
v___jp_1587_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = l_Lean_Expr_getAppNumArgs(v_e_1566_);
v___x_1596_ = lean_nat_sub(v___x_1595_, v___x_1594_);
lean_dec(v___x_1595_);
v___x_1597_ = lean_nat_sub(v___x_1596_, v___x_1594_);
lean_dec(v___x_1596_);
v___x_1598_ = l_Lean_Expr_getRevArg_x21(v_e_1566_, v___x_1597_);
lean_dec_ref(v_e_1566_);
v___x_1599_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v___x_1598_, v___y_1590_, v___y_1592_, v___y_1589_, v___y_1588_, v___y_1593_, v___y_1591_);
return v___x_1599_;
}
v___jp_1600_:
{
uint8_t v___x_1612_; 
v___x_1612_ = l_Lean_Expr_isFVar(v_e_1566_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v_e_1566_);
v___x_1613_ = lean_box(1);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
else
{
lean_object* v___x_1615_; 
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1608_);
lean_inc_ref(v_e_1566_);
v___x_1615_ = lean_infer_type(v_e_1566_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_Meta_whnfD(v_a_1616_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_n(v_a_1618_, 2);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1620_ = l_Lean_MessageData_ofExpr(v_e_1566_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_indentExpr(v_a_1618_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Lean_Expr_getAppFn(v_a_1618_);
lean_dec(v_a_1618_);
if (lean_obj_tag(v___x_1626_) == 4)
{
lean_object* v_declName_1627_; lean_object* v___x_1628_; 
v_declName_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_declName_1627_);
lean_dec_ref_known(v___x_1626_, 2);
v___x_1628_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1627_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1661_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1661_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1661_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
if (lean_obj_tag(v_a_1629_) == 5)
{
lean_object* v_val_1633_; lean_object* v_ctors_1634_; uint8_t v_isRec_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_dec_ref_known(v___x_1625_, 2);
v_val_1633_ = lean_ctor_get(v_a_1629_, 0);
lean_inc_ref(v_val_1633_);
lean_dec_ref_known(v_a_1629_, 1);
v_ctors_1634_ = lean_ctor_get(v_val_1633_, 4);
lean_inc(v_ctors_1634_);
v_isRec_1635_ = lean_ctor_get_uint8(v_val_1633_, sizeof(void*)*6);
lean_dec_ref(v_val_1633_);
v___x_1636_ = l_List_lengthTR___redArg(v_ctors_1634_);
lean_dec(v_ctors_1634_);
v___x_1637_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*1, v_isRec_1635_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*1 + 1, v___y_1601_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1637_);
v___x_1639_ = v___x_1631_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v___x_1641_; 
lean_del_object(v___x_1631_);
lean_dec(v_a_1629_);
v___x_1641_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1606_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; uint8_t v_verbose_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_verbose_1643_ = lean_ctor_get_uint8(v_a_1642_, 0);
lean_dec(v_a_1642_);
if (v_verbose_1643_ == 0)
{
lean_dec_ref_known(v___x_1625_, 2);
goto v___jp_1581_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Sym_reportIssue(v___x_1625_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_dec_ref_known(v___x_1644_, 1);
goto v___jp_1581_;
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
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
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref_known(v___x_1625_, 2);
v_a_1653_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1641_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1641_);
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
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref_known(v___x_1625_, 2);
v_a_1662_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1628_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1628_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v___x_1670_; 
lean_dec_ref(v___x_1626_);
v___x_1670_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1606_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; uint8_t v_verbose_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v_verbose_1672_ = lean_ctor_get_uint8(v_a_1671_, 0);
lean_dec(v_a_1671_);
if (v_verbose_1672_ == 0)
{
lean_dec_ref_known(v___x_1625_, 2);
goto v___jp_1584_;
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Meta_Sym_reportIssue(v___x_1625_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_dec_ref_known(v___x_1673_, 1);
goto v___jp_1584_;
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref_known(v___x_1625_, 2);
v_a_1682_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1670_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1670_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v_e_1566_);
v_a_1690_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1617_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1617_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_e_1566_);
v_a_1698_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1615_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1615_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
v___jp_1706_:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_Meta_Grind_isIte(v_e_1566_);
if (v___x_1717_ == 0)
{
uint8_t v___x_1718_; 
v___x_1718_ = l_Lean_Meta_Grind_isDIte(v_e_1566_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1566_, v___y_1707_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; uint8_t v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_inc_ref(v_e_1566_);
v___x_1722_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1566_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1782_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1782_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1782_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_unbox(v_a_1723_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v_env_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_st_ref_get(v___y_1716_);
v_env_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref(v_env_1729_);
lean_dec(v___x_1728_);
v___x_1730_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1729_, v_e_1566_);
if (lean_obj_tag(v___x_1730_) == 1)
{
lean_object* v_val_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; uint8_t v___x_1735_; lean_object* v___x_1737_; 
lean_dec_ref(v_e_1566_);
v_val_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1731_);
lean_dec(v_val_1731_);
v___x_1733_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___x_1734_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*1, v___x_1734_);
v___x_1735_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*1 + 1, v___x_1735_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1733_);
v___x_1737_ = v___x_1725_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1733_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v___x_1730_);
lean_del_object(v___x_1725_);
v___x_1739_ = l_Lean_Expr_getAppFn(v_e_1566_);
if (lean_obj_tag(v___x_1739_) == 4)
{
lean_object* v_declName_1740_; lean_object* v___x_1741_; 
v_declName_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_declName_1740_);
lean_dec_ref_known(v___x_1739_, 2);
v___x_1741_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1740_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
if (lean_obj_tag(v_a_1742_) == 1)
{
lean_object* v_val_1743_; lean_object* v___x_1744_; 
v_val_1743_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v_a_1742_, 1);
lean_inc_ref(v_e_1566_);
v___x_1744_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1566_, v___y_1707_, v___y_1711_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1759_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1759_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1759_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_unbox(v_a_1745_);
lean_dec(v_a_1745_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
lean_del_object(v___x_1747_);
lean_dec(v_val_1743_);
v___x_1750_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
v___y_1601_ = v___x_1750_;
v___y_1602_ = v___y_1707_;
v___y_1603_ = v___y_1708_;
v___y_1604_ = v___y_1709_;
v___y_1605_ = v___y_1710_;
v___y_1606_ = v___y_1711_;
v___y_1607_ = v___y_1712_;
v___y_1608_ = v___y_1713_;
v___y_1609_ = v___y_1714_;
v___y_1610_ = v___y_1715_;
v___y_1611_ = v___y_1716_;
goto v___jp_1600_;
}
else
{
lean_object* v_ctors_1751_; uint8_t v_isRec_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1757_; 
lean_dec_ref(v_e_1566_);
v_ctors_1751_ = lean_ctor_get(v_val_1743_, 4);
lean_inc(v_ctors_1751_);
v_isRec_1752_ = lean_ctor_get_uint8(v_val_1743_, sizeof(void*)*6);
lean_dec(v_val_1743_);
v___x_1753_ = l_List_lengthTR___redArg(v_ctors_1751_);
lean_dec(v_ctors_1751_);
v___x_1754_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1, v_isRec_1752_);
v___x_1755_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1 + 1, v___x_1755_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1754_);
v___x_1757_ = v___x_1747_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1754_);
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
lean_dec(v_val_1743_);
lean_dec(v_a_1723_);
lean_dec_ref(v_e_1566_);
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
else
{
uint8_t v___x_1768_; 
lean_dec(v_a_1742_);
v___x_1768_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
v___y_1601_ = v___x_1768_;
v___y_1602_ = v___y_1707_;
v___y_1603_ = v___y_1708_;
v___y_1604_ = v___y_1709_;
v___y_1605_ = v___y_1710_;
v___y_1606_ = v___y_1711_;
v___y_1607_ = v___y_1712_;
v___y_1608_ = v___y_1713_;
v___y_1609_ = v___y_1714_;
v___y_1610_ = v___y_1715_;
v___y_1611_ = v___y_1716_;
goto v___jp_1600_;
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1723_);
lean_dec_ref(v_e_1566_);
v_a_1769_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1741_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1741_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
uint8_t v___x_1777_; 
lean_dec_ref(v___x_1739_);
v___x_1777_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
v___y_1601_ = v___x_1777_;
v___y_1602_ = v___y_1707_;
v___y_1603_ = v___y_1708_;
v___y_1604_ = v___y_1709_;
v___y_1605_ = v___y_1710_;
v___y_1606_ = v___y_1711_;
v___y_1607_ = v___y_1712_;
v___y_1608_ = v___y_1713_;
v___y_1609_ = v___y_1714_;
v___y_1610_ = v___y_1715_;
v___y_1611_ = v___y_1716_;
goto v___jp_1600_;
}
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
lean_dec(v_a_1723_);
lean_dec_ref(v_e_1566_);
v___x_1778_ = lean_box(0);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1778_);
v___x_1780_ = v___x_1725_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v_e_1566_);
v_a_1783_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1722_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1722_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_toCold_1791_; lean_object* v_options_1792_; uint8_t v_hasTrace_1793_; 
v_toCold_1791_ = lean_ctor_get(v___y_1715_, 0);
v_options_1792_ = lean_ctor_get(v_toCold_1791_, 2);
v_hasTrace_1793_ = lean_ctor_get_uint8(v_options_1792_, sizeof(void*)*1);
if (v_hasTrace_1793_ == 0)
{
lean_dec_ref(v_e_1566_);
goto v___jp_1578_;
}
else
{
lean_object* v_inheritedTraceOptions_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_inheritedTraceOptions_1794_ = lean_ctor_get(v_toCold_1791_, 11);
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1794_, v_options_1792_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v_e_1566_);
goto v___jp_1578_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Meta_Grind_updateLastTag(v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref_known(v___x_1798_, 1);
v___x_1799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1800_ = l_Lean_MessageData_ofExpr(v_e_1566_);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1795_, v___x_1801_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref_known(v___x_1802_, 1);
goto v___jp_1578_;
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_e_1566_);
v_a_1811_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1798_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1798_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v_e_1566_);
v_a_1819_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1719_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1719_);
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
else
{
v___y_1588_ = v___y_1714_;
v___y_1589_ = v___y_1713_;
v___y_1590_ = v___y_1707_;
v___y_1591_ = v___y_1716_;
v___y_1592_ = v___y_1711_;
v___y_1593_ = v___y_1715_;
goto v___jp_1587_;
}
}
else
{
v___y_1588_ = v___y_1714_;
v___y_1589_ = v___y_1713_;
v___y_1590_ = v___y_1707_;
v___y_1591_ = v___y_1716_;
v___y_1592_ = v___y_1711_;
v___y_1593_ = v___y_1715_;
goto v___jp_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec(v_a_1869_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1881_, lean_object* v_msg_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1881_, v_msg_1882_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1895_, lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1895_, v_msg_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1909_, lean_object* v_constName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_constName_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1923_, v_constName_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1925_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1937_, lean_object* v_ref_1938_, lean_object* v_constName_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1938_, v_constName_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_ref_1953_, lean_object* v_constName_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1952_, v_ref_1953_, v_constName_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v_ref_1953_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1967_, lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v_declHint_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1968_, v_msg_1969_, v_declHint_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_ref_1984_, lean_object* v_msg_1985_, lean_object* v_declHint_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1983_, v_ref_1984_, v_msg_1985_, v_declHint_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v_ref_1984_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1999_, lean_object* v_declHint_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1999_, v_declHint_2000_, v___y_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2013_, lean_object* v_declHint_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2013_, v_declHint_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2027_, lean_object* v_ref_2028_, lean_object* v_msg_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2028_, v_msg_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2042_, lean_object* v_ref_2043_, lean_object* v_msg_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2042_, v_ref_2043_, v_msg_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec(v_ref_2043_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2057_, lean_object* v_msg_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2058_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2071_, lean_object* v_msg_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2071_, v_msg_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec(v___y_2073_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_box(0);
return v___x_2087_;
}
else
{
lean_object* v_key_2088_; lean_object* v_value_2089_; lean_object* v_tail_2090_; lean_object* v_fst_2091_; lean_object* v_snd_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; uint8_t v___x_2095_; 
v_key_2088_ = lean_ctor_get(v_x_2086_, 0);
v_value_2089_ = lean_ctor_get(v_x_2086_, 1);
v_tail_2090_ = lean_ctor_get(v_x_2086_, 2);
v_fst_2091_ = lean_ctor_get(v_key_2088_, 0);
v_snd_2092_ = lean_ctor_get(v_key_2088_, 1);
v_fst_2093_ = lean_ctor_get(v_a_2085_, 0);
v_snd_2094_ = lean_ctor_get(v_a_2085_, 1);
v___x_2095_ = lean_expr_eqv(v_fst_2091_, v_fst_2093_);
if (v___x_2095_ == 0)
{
v_x_2086_ = v_tail_2090_;
goto _start;
}
else
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_expr_eqv(v_snd_2092_, v_snd_2094_);
if (v___x_2097_ == 0)
{
v_x_2086_ = v_tail_2090_;
goto _start;
}
else
{
lean_object* v___x_2099_; 
lean_inc(v_value_2089_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_value_2089_);
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2100_, lean_object* v_x_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2100_, v_x_2101_);
lean_dec(v_x_2101_);
lean_dec_ref(v_a_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_buckets_2105_; lean_object* v_fst_2106_; lean_object* v_snd_2107_; lean_object* v___x_2108_; uint64_t v___x_2109_; uint64_t v___x_2110_; uint64_t v___x_2111_; uint64_t v___x_2112_; uint64_t v___x_2113_; uint64_t v_fold_2114_; uint64_t v___x_2115_; uint64_t v___x_2116_; uint64_t v___x_2117_; size_t v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_buckets_2105_ = lean_ctor_get(v_m_2103_, 1);
v_fst_2106_ = lean_ctor_get(v_a_2104_, 0);
v_snd_2107_ = lean_ctor_get(v_a_2104_, 1);
v___x_2108_ = lean_array_get_size(v_buckets_2105_);
v___x_2109_ = l_Lean_Expr_hash(v_fst_2106_);
v___x_2110_ = l_Lean_Expr_hash(v_snd_2107_);
v___x_2111_ = lean_uint64_mix_hash(v___x_2109_, v___x_2110_);
v___x_2112_ = 32ULL;
v___x_2113_ = lean_uint64_shift_right(v___x_2111_, v___x_2112_);
v_fold_2114_ = lean_uint64_xor(v___x_2111_, v___x_2113_);
v___x_2115_ = 16ULL;
v___x_2116_ = lean_uint64_shift_right(v_fold_2114_, v___x_2115_);
v___x_2117_ = lean_uint64_xor(v_fold_2114_, v___x_2116_);
v___x_2118_ = lean_uint64_to_usize(v___x_2117_);
v___x_2119_ = lean_usize_of_nat(v___x_2108_);
v___x_2120_ = ((size_t)1ULL);
v___x_2121_ = lean_usize_sub(v___x_2119_, v___x_2120_);
v___x_2122_ = lean_usize_land(v___x_2118_, v___x_2121_);
v___x_2123_ = lean_array_uget_borrowed(v_buckets_2105_, v___x_2122_);
v___x_2124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2104_, v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2125_, v_a_2126_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_m_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2128_, uint8_t v___x_2129_, lean_object* v_fst_2130_, lean_object* v_snd_2131_, lean_object* v___x_2132_, lean_object* v_____r_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2145_ = lean_unsigned_to_nat(2u);
v___x_2146_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1, v_a_2128_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 1, v___x_2129_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_fst_2130_);
lean_ctor_set(v___x_2148_, 1, v_snd_2131_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2132_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2147_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2153_ = _args[0];
lean_object* v___x_2154_ = _args[1];
lean_object* v_fst_2155_ = _args[2];
lean_object* v_snd_2156_ = _args[3];
lean_object* v___x_2157_ = _args[4];
lean_object* v_____r_2158_ = _args[5];
lean_object* v___y_2159_ = _args[6];
lean_object* v___y_2160_ = _args[7];
lean_object* v___y_2161_ = _args[8];
lean_object* v___y_2162_ = _args[9];
lean_object* v___y_2163_ = _args[10];
lean_object* v___y_2164_ = _args[11];
lean_object* v___y_2165_ = _args[12];
lean_object* v___y_2166_ = _args[13];
lean_object* v___y_2167_ = _args[14];
lean_object* v___y_2168_ = _args[15];
lean_object* v___y_2169_ = _args[16];
_start:
{
uint8_t v_a_34317__boxed_2170_; uint8_t v___x_34318__boxed_2171_; lean_object* v_res_2172_; 
v_a_34317__boxed_2170_ = lean_unbox(v_a_2153_);
v___x_34318__boxed_2171_ = lean_unbox(v___x_2154_);
v_res_2172_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34317__boxed_2170_, v___x_34318__boxed_2171_, v_fst_2155_, v_snd_2156_, v___x_2157_, v_____r_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec(v___y_2159_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2173_, lean_object* v_snd_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v_____r_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2189_ = l_Lean_Expr_appFn_x21(v_fst_2173_);
v___x_2190_ = l_Lean_Expr_appFn_x21(v_snd_2174_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2175_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2176_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2196_, lean_object* v_snd_2197_, lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v_____r_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2196_, v_snd_2197_, v___x_2198_, v___x_2199_, v_____r_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec(v_snd_2197_);
lean_dec(v_fst_2196_);
return v_res_2212_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___f_2214_; 
v___x_2213_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2214_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2214_, 0, v___x_2213_);
return v___f_2214_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2220_ = l_Lean_Name_append(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2239_, lean_object* v___y_2240_, lean_object* v_eq_2241_, lean_object* v_a_2242_, lean_object* v_b_2243_, lean_object* v_a_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___y_2257_; lean_object* v_snd_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2399_; 
v_snd_2277_ = lean_ctor_get(v_a_2244_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_a_2244_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v_a_2244_, 0);
lean_dec(v_unused_2400_);
v___x_2279_ = v_a_2244_;
v_isShared_2280_ = v_isSharedCheck_2399_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_snd_2277_);
lean_dec(v_a_2244_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2399_;
goto v_resetjp_2278_;
}
v___jp_2256_:
{
if (lean_obj_tag(v___y_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2268_; 
v_a_2258_ = lean_ctor_get(v___y_2257_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___y_2257_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2260_ = v___y_2257_;
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___y_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
if (lean_obj_tag(v_a_2258_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; 
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v_a_2262_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v_a_2258_, 1);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v_a_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v_a_2266_; 
lean_del_object(v___x_2260_);
v_a_2266_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v_a_2258_, 1);
v_a_2244_ = v_a_2266_;
goto _start;
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v_a_2269_ = lean_ctor_get(v___y_2257_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___y_2257_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___y_2257_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___y_2257_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
v_resetjp_2278_:
{
lean_object* v_snd_2281_; lean_object* v_fst_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2398_; 
v_snd_2281_ = lean_ctor_get(v_snd_2277_, 1);
v_fst_2282_ = lean_ctor_get(v_snd_2277_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_snd_2277_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2284_ = v_snd_2277_;
v_isShared_2285_ = v_isSharedCheck_2398_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_snd_2281_);
lean_inc(v_fst_2282_);
lean_dec(v_snd_2277_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2398_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_fst_2286_; lean_object* v_snd_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2397_; 
v_fst_2286_ = lean_ctor_get(v_snd_2281_, 0);
v_snd_2287_ = lean_ctor_get(v_snd_2281_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_snd_2281_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2289_ = v_snd_2281_;
v_isShared_2290_ = v_isSharedCheck_2397_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_snd_2287_);
lean_inc(v_fst_2286_);
lean_dec(v_snd_2281_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2397_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
uint8_t v___y_2292_; uint8_t v___x_2306_; 
v___x_2306_ = l_Lean_Expr_isApp(v_fst_2286_);
if (v___x_2306_ == 0)
{
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v___y_2292_ = v_a_2239_;
goto v___jp_2291_;
}
else
{
uint8_t v___x_2307_; 
v___x_2307_ = l_Lean_Expr_isApp(v_snd_2287_);
if (v___x_2307_ == 0)
{
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v___y_2292_ = v___x_2307_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___f_2311_; uint8_t v___x_2312_; 
lean_del_object(v___x_2289_);
lean_del_object(v___x_2284_);
lean_del_object(v___x_2279_);
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_nat_sub(v_fst_2282_, v___x_2309_);
lean_dec(v_fst_2282_);
v___f_2311_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2240_);
lean_inc(v___x_2310_);
v___x_2312_ = l_List_elem___redArg(v___f_2311_, v___x_2310_, v___y_2240_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = l_Lean_Expr_appArg_x21(v_fst_2286_);
v___x_2314_ = l_Lean_Expr_appArg_x21(v_snd_2287_);
v___x_2315_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2313_, v___x_2314_, v___y_2245_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_unbox(v_a_2316_);
if (v___x_2317_ == 0)
{
lean_object* v_toCold_2318_; lean_object* v_options_2319_; lean_object* v_inheritedTraceOptions_2320_; uint8_t v_hasTrace_2321_; 
v_toCold_2318_ = lean_ctor_get(v___y_2253_, 0);
v_options_2319_ = lean_ctor_get(v_toCold_2318_, 2);
v_inheritedTraceOptions_2320_ = lean_ctor_get(v_toCold_2318_, 11);
v_hasTrace_2321_ = lean_ctor_get_uint8(v_options_2319_, sizeof(void*)*1);
if (v_hasTrace_2321_ == 0)
{
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2327_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2328_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2320_, v_options_2319_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_Grind_updateLastTag(v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v___x_2330_; 
lean_dec_ref_known(v___x_2329_, 1);
v___x_2330_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2241_, v___y_2245_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2242_);
v___x_2333_ = l_Lean_MessageData_ofExpr(v_a_2242_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
lean_inc_ref(v_b_2243_);
v___x_2337_ = l_Lean_MessageData_ofExpr(v_b_2243_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
lean_inc_ref(v_eq_2241_);
v___x_2341_ = l_Lean_MessageData_ofExpr(v_eq_2241_);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_MessageData_ofExpr(v___x_2313_);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_MessageData_ofExpr(v___x_2314_);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = l_Nat_reprFast(v_a_2331_);
v___x_2354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
v___x_2355_ = l_Lean_MessageData_ofFormat(v___x_2354_);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2352_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2326_, v___x_2356_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
v___x_2360_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2359_, v___x_2307_, v_fst_2286_, v_snd_2287_, v___x_2310_, v_a_2358_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
v___y_2257_ = v___x_2360_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v_a_2316_);
lean_dec(v___x_2310_);
lean_dec(v_snd_2287_);
lean_dec(v_fst_2286_);
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v_a_2361_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2357_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2357_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2316_);
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
lean_dec(v___x_2310_);
lean_dec(v_snd_2287_);
lean_dec(v_fst_2286_);
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v_a_2369_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2330_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2330_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2316_);
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
lean_dec(v___x_2310_);
lean_dec(v_snd_2287_);
lean_dec(v_fst_2286_);
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v_a_2377_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2329_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2329_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
v___jp_2322_:
{
lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
v___x_2325_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2324_, v___x_2307_, v_fst_2286_, v_snd_2287_, v___x_2310_, v___x_2323_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
v___y_2257_ = v___x_2325_;
goto v___jp_2256_;
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v_a_2316_);
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
v___x_2385_ = lean_box(0);
v___x_2386_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2286_, v_snd_2287_, v___x_2310_, v___x_2308_, v___x_2385_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v_snd_2287_);
lean_dec(v_fst_2286_);
v___y_2257_ = v___x_2386_;
goto v___jp_2256_;
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
lean_dec(v___x_2310_);
lean_dec(v_snd_2287_);
lean_dec(v_fst_2286_);
lean_dec_ref(v_b_2243_);
lean_dec_ref(v_a_2242_);
lean_dec_ref(v_eq_2241_);
lean_dec(v___y_2240_);
v_a_2387_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2315_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2315_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_box(0);
v___x_2396_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2286_, v_snd_2287_, v___x_2310_, v___x_2308_, v___x_2395_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v_snd_2287_);
lean_dec(v_fst_2286_);
v___y_2257_ = v___x_2396_;
goto v___jp_2256_;
}
}
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2293_ = lean_unsigned_to_nat(2u);
v___x_2294_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*1, v___y_2292_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*1 + 1, v___y_2292_);
v___x_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
if (v_isShared_2290_ == 0)
{
v___x_2297_ = v___x_2289_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_fst_2286_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_snd_2287_);
v___x_2297_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2299_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 1, v___x_2297_);
v___x_2299_ = v___x_2284_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_fst_2282_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v___x_2299_);
lean_ctor_set(v___x_2279_, 0, v___x_2295_);
v___x_2301_ = v___x_2279_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_a_2401_ = _args[0];
lean_object* v___y_2402_ = _args[1];
lean_object* v_eq_2403_ = _args[2];
lean_object* v_a_2404_ = _args[3];
lean_object* v_b_2405_ = _args[4];
lean_object* v_a_2406_ = _args[5];
lean_object* v___y_2407_ = _args[6];
lean_object* v___y_2408_ = _args[7];
lean_object* v___y_2409_ = _args[8];
lean_object* v___y_2410_ = _args[9];
lean_object* v___y_2411_ = _args[10];
lean_object* v___y_2412_ = _args[11];
lean_object* v___y_2413_ = _args[12];
lean_object* v___y_2414_ = _args[13];
lean_object* v___y_2415_ = _args[14];
lean_object* v___y_2416_ = _args[15];
lean_object* v___y_2417_ = _args[16];
_start:
{
uint8_t v_a_34491__boxed_2418_; lean_object* v_res_2419_; 
v_a_34491__boxed_2418_ = lean_unbox(v_a_2401_);
v_res_2419_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34491__boxed_2418_, v___y_2402_, v_eq_2403_, v_a_2404_, v_b_2405_, v_a_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec(v___y_2407_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2420_, lean_object* v_b_2421_, lean_object* v_eq_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v___x_2437_; 
lean_inc_ref(v_eq_2422_);
v___x_2437_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2422_, v_a_2423_, v_a_2427_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; uint8_t v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = lean_unbox(v_a_2438_);
lean_dec(v_a_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
lean_inc_ref(v_eq_2422_);
v___x_2440_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2422_, v_a_2423_, v_a_2427_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; uint8_t v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = lean_unbox(v_a_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___y_2445_; lean_object* v_toGoalState_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2490_; 
v___x_2443_ = lean_st_ref_get(v_a_2423_);
v_toGoalState_2478_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2443_, 1);
lean_dec(v_unused_2491_);
v___x_2480_ = v___x_2443_;
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_toGoalState_2478_);
lean_dec(v___x_2443_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
v___jp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2446_ = l_Lean_Expr_getAppNumArgs(v_a_2420_);
v___x_2447_ = lean_box(0);
lean_inc_ref(v_b_2421_);
lean_inc_ref(v_a_2420_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2420_);
lean_ctor_set(v___x_2448_, 1, v_b_2421_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2446_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2447_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_unbox(v_a_2441_);
v___x_2452_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___x_2451_, v___y_2445_, v_eq_2422_, v_a_2420_, v_b_2421_, v___x_2450_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2469_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_fst_2457_; 
v_fst_2457_ = lean_ctor_get(v_a_2453_, 0);
lean_inc(v_fst_2457_);
lean_dec(v_a_2453_);
if (lean_obj_tag(v_fst_2457_) == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2463_; 
v___x_2458_ = lean_unsigned_to_nat(2u);
v___x_2459_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
v___x_2460_ = lean_unbox(v_a_2441_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1, v___x_2460_);
v___x_2461_ = lean_unbox(v_a_2441_);
lean_dec(v_a_2441_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1 + 1, v___x_2461_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2459_);
v___x_2463_ = v___x_2455_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2459_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2467_; 
lean_dec(v_a_2441_);
v_val_2465_ = lean_ctor_get(v_fst_2457_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v_fst_2457_, 1);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_val_2465_);
v___x_2467_ = v___x_2455_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_val_2465_);
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
lean_dec(v_a_2441_);
v_a_2470_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2452_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2452_);
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
v_resetjp_2479_:
{
lean_object* v_split_2482_; lean_object* v_argPosMap_2483_; lean_object* v___x_2485_; 
v_split_2482_ = lean_ctor_get(v_toGoalState_2478_, 15);
lean_inc_ref(v_split_2482_);
lean_dec_ref(v_toGoalState_2478_);
v_argPosMap_2483_ = lean_ctor_get(v_split_2482_, 5);
lean_inc_ref(v_argPosMap_2483_);
lean_dec_ref(v_split_2482_);
lean_inc_ref(v_b_2421_);
lean_inc_ref(v_a_2420_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_b_2421_);
lean_ctor_set(v___x_2480_, 0, v_a_2420_);
v___x_2485_ = v___x_2480_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2420_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_b_2421_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2483_, v___x_2485_);
lean_dec_ref(v___x_2485_);
lean_dec_ref(v_argPosMap_2483_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_box(0);
v___y_2445_ = v___x_2487_;
goto v___jp_2444_;
}
else
{
lean_object* v_val_2488_; 
v_val_2488_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v___x_2486_, 1);
v___y_2445_ = v_val_2488_;
goto v___jp_2444_;
}
}
}
}
else
{
lean_dec(v_a_2441_);
lean_dec_ref(v_eq_2422_);
lean_dec_ref(v_b_2421_);
lean_dec_ref(v_a_2420_);
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec_ref(v_eq_2422_);
lean_dec_ref(v_b_2421_);
lean_dec_ref(v_a_2420_);
v_a_2492_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2440_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2440_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_dec_ref(v_eq_2422_);
lean_dec_ref(v_b_2421_);
lean_dec_ref(v_a_2420_);
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref(v_eq_2422_);
lean_dec_ref(v_b_2421_);
lean_dec_ref(v_a_2420_);
v_a_2500_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2437_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2437_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
v___jp_2434_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2508_, lean_object* v_b_2509_, lean_object* v_eq_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2508_, v_b_2509_, v_eq_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec(v_a_2511_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2523_, lean_object* v___y_2524_, lean_object* v_eq_2525_, lean_object* v_a_2526_, lean_object* v_b_2527_, lean_object* v_inst_2528_, lean_object* v_a_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2523_, v___y_2524_, v_eq_2525_, v_a_2526_, v_b_2527_, v_a_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2542_ = _args[0];
lean_object* v___y_2543_ = _args[1];
lean_object* v_eq_2544_ = _args[2];
lean_object* v_a_2545_ = _args[3];
lean_object* v_b_2546_ = _args[4];
lean_object* v_inst_2547_ = _args[5];
lean_object* v_a_2548_ = _args[6];
lean_object* v___y_2549_ = _args[7];
lean_object* v___y_2550_ = _args[8];
lean_object* v___y_2551_ = _args[9];
lean_object* v___y_2552_ = _args[10];
lean_object* v___y_2553_ = _args[11];
lean_object* v___y_2554_ = _args[12];
lean_object* v___y_2555_ = _args[13];
lean_object* v___y_2556_ = _args[14];
lean_object* v___y_2557_ = _args[15];
lean_object* v___y_2558_ = _args[16];
lean_object* v___y_2559_ = _args[17];
_start:
{
uint8_t v_a_34972__boxed_2560_; lean_object* v_res_2561_; 
v_a_34972__boxed_2560_ = lean_unbox(v_a_2542_);
v_res_2561_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34972__boxed_2560_, v___y_2543_, v_eq_2544_, v_a_2545_, v_b_2546_, v_inst_2547_, v_a_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec(v___y_2549_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2562_, lean_object* v_m_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2563_, v_a_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2566_, lean_object* v_m_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2566_, v_m_2567_, v_a_2568_);
lean_dec_ref(v_a_2568_);
lean_dec_ref(v_m_2567_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2570_, lean_object* v_a_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2571_, v_x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2574_, lean_object* v_a_2575_, lean_object* v_x_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2574_, v_a_2575_, v_x_2576_);
lean_dec(v_x_2576_);
lean_dec_ref(v_a_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2592_; 
lean_inc_ref(v_imp_2578_);
v___x_2592_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; uint8_t v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = lean_unbox(v_a_2593_);
lean_dec(v_a_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2609_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2609_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2609_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2601_ = lean_box(1);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_box(0);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2605_);
v___x_2607_ = v___x_2598_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2595_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2595_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_binderType_2618_; lean_object* v_body_2619_; lean_object* v___x_2620_; 
v_binderType_2618_ = lean_ctor_get(v_imp_2578_, 1);
lean_inc_ref_n(v_binderType_2618_, 2);
v_body_2619_ = lean_ctor_get(v_imp_2578_, 2);
lean_inc_ref(v_body_2619_);
lean_dec_ref(v_imp_2578_);
v___x_2620_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2618_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; uint8_t v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_unbox(v_a_2621_);
lean_dec(v_a_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2618_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2660_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2660_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2660_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
uint8_t v___x_2636_; 
v___x_2636_ = lean_unbox(v_a_2624_);
if (v___x_2636_ == 0)
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Expr_hasLooseBVars(v_body_2619_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_inc_ref(v_body_2619_);
v___x_2638_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2619_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; uint8_t v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = lean_unbox(v_a_2639_);
lean_dec(v_a_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2619_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; uint8_t v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = lean_unbox(v_a_2642_);
lean_dec(v_a_2642_);
if (v___x_2643_ == 0)
{
goto v___jp_2628_;
}
else
{
lean_del_object(v___x_2626_);
lean_dec(v_a_2624_);
goto v___jp_2586_;
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2626_);
lean_dec(v_a_2624_);
v_a_2644_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2641_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2641_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_del_object(v___x_2626_);
lean_dec(v_a_2624_);
lean_dec_ref(v_body_2619_);
goto v___jp_2586_;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2626_);
lean_dec(v_a_2624_);
lean_dec_ref(v_body_2619_);
v_a_2652_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2638_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2638_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_dec_ref(v_body_2619_);
goto v___jp_2628_;
}
}
else
{
lean_del_object(v___x_2626_);
lean_dec(v_a_2624_);
lean_dec_ref(v_body_2619_);
goto v___jp_2589_;
}
v___jp_2628_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2634_; 
v___x_2629_ = lean_unsigned_to_nat(2u);
v___x_2630_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = lean_unbox(v_a_2624_);
lean_ctor_set_uint8(v___x_2630_, sizeof(void*)*1, v___x_2631_);
v___x_2632_ = lean_unbox(v_a_2624_);
lean_dec(v_a_2624_);
lean_ctor_set_uint8(v___x_2630_, sizeof(void*)*1 + 1, v___x_2632_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2630_);
v___x_2634_ = v___x_2626_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2630_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v_body_2619_);
v_a_2661_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2623_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2623_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_dec_ref(v_body_2619_);
lean_dec_ref(v_binderType_2618_);
goto v___jp_2589_;
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v_body_2619_);
lean_dec_ref(v_binderType_2618_);
v_a_2669_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2620_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2620_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref(v_imp_2578_);
v_a_2677_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2592_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2592_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
v___jp_2586_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
v___jp_2589_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2694_, lean_object* v_h_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2694_, v_a_2696_, v_a_2700_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2708_, lean_object* v_h_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2708_, v_h_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec(v_a_2710_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
switch(lean_obj_tag(v_s_2722_))
{
case 0:
{
lean_object* v_e_2734_; lean_object* v___x_2735_; 
v_e_2734_ = lean_ctor_get(v_s_2722_, 0);
lean_inc_ref(v_e_2734_);
lean_dec_ref_known(v_s_2722_, 2);
v___x_2735_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2734_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
return v___x_2735_;
}
case 1:
{
lean_object* v_e_2736_; lean_object* v___x_2737_; 
v_e_2736_ = lean_ctor_get(v_s_2722_, 0);
lean_inc_ref(v_e_2736_);
lean_dec_ref_known(v_s_2722_, 2);
v___x_2737_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2736_, v_a_2723_, v_a_2727_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
return v___x_2737_;
}
default: 
{
lean_object* v_a_2738_; lean_object* v_b_2739_; lean_object* v_eq_2740_; lean_object* v___x_2741_; 
v_a_2738_ = lean_ctor_get(v_s_2722_, 0);
lean_inc_ref(v_a_2738_);
v_b_2739_ = lean_ctor_get(v_s_2722_, 1);
lean_inc_ref(v_b_2739_);
v_eq_2740_ = lean_ctor_get(v_s_2722_, 3);
lean_inc_ref(v_eq_2740_);
lean_dec_ref_known(v_s_2722_, 5);
v___x_2741_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2738_, v_b_2739_, v_eq_2740_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec(v_a_2743_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_obj_tag_nat(v_x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2757_);
lean_dec(v_x_2757_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2759_, lean_object* v_k_2760_){
_start:
{
if (lean_obj_tag(v_t_2759_) == 0)
{
return v_k_2760_;
}
else
{
lean_object* v_c_2761_; lean_object* v_numCases_2762_; uint8_t v_isRec_2763_; uint8_t v_tryPostpone_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_c_2761_ = lean_ctor_get(v_t_2759_, 0);
lean_inc_ref(v_c_2761_);
v_numCases_2762_ = lean_ctor_get(v_t_2759_, 1);
lean_inc(v_numCases_2762_);
v_isRec_2763_ = lean_ctor_get_uint8(v_t_2759_, sizeof(void*)*2);
v_tryPostpone_2764_ = lean_ctor_get_uint8(v_t_2759_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2759_, 2);
v___x_2765_ = lean_box(v_isRec_2763_);
v___x_2766_ = lean_box(v_tryPostpone_2764_);
v___x_2767_ = lean_apply_4(v_k_2760_, v_c_2761_, v_numCases_2762_, v___x_2765_, v___x_2766_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2768_, lean_object* v_ctorIdx_2769_, lean_object* v_t_2770_, lean_object* v_h_2771_, lean_object* v_k_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2770_, v_k_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2774_, lean_object* v_ctorIdx_2775_, lean_object* v_t_2776_, lean_object* v_h_2777_, lean_object* v_k_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2774_, v_ctorIdx_2775_, v_t_2776_, v_h_2777_, v_k_2778_);
lean_dec(v_ctorIdx_2775_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2780_, lean_object* v_none_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2780_, v_none_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2783_, lean_object* v_t_2784_, lean_object* v_h_2785_, lean_object* v_none_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2784_, v_none_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2788_, lean_object* v_some_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2788_, v_some_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2791_, lean_object* v_t_2792_, lean_object* v_h_2793_, lean_object* v_some_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2792_, v_some_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2796_, lean_object* v_as_2797_, size_t v_i_2798_, size_t v_stop_2799_){
_start:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_usize_dec_eq(v_i_2798_, v_stop_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2801_ = lean_array_uget_borrowed(v_as_2797_, v_i_2798_);
v___x_2802_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2801_, v_a_2796_);
if (v___x_2802_ == 0)
{
size_t v___x_2803_; size_t v___x_2804_; 
v___x_2803_ = ((size_t)1ULL);
v___x_2804_ = lean_usize_add(v_i_2798_, v___x_2803_);
v_i_2798_ = v___x_2804_;
goto _start;
}
else
{
return v___x_2802_;
}
}
else
{
uint8_t v___x_2806_; 
v___x_2806_ = 0;
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2807_, lean_object* v_as_2808_, lean_object* v_i_2809_, lean_object* v_stop_2810_){
_start:
{
uint64_t v_a_2507__boxed_2811_; size_t v_i_boxed_2812_; size_t v_stop_boxed_2813_; uint8_t v_res_2814_; lean_object* v_r_2815_; 
v_a_2507__boxed_2811_ = lean_unbox_uint64(v_a_2807_);
lean_dec_ref(v_a_2807_);
v_i_boxed_2812_ = lean_unbox_usize(v_i_2809_);
lean_dec(v_i_2809_);
v_stop_boxed_2813_ = lean_unbox_usize(v_stop_2810_);
lean_dec(v_stop_2810_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2811_, v_as_2808_, v_i_boxed_2812_, v_stop_boxed_2813_);
lean_dec_ref(v_as_2808_);
v_r_2815_ = lean_box(v_res_2814_);
return v_r_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2818_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2871_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2871_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2871_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
if (lean_obj_tag(v_a_2828_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2830_);
v_val_2832_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_a_2828_, 1);
v___x_2833_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2857_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2857_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2857_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2838_ = lean_unsigned_to_nat(0u);
v___x_2839_ = lean_array_get_size(v_val_2832_);
v___x_2840_ = lean_nat_dec_lt(v___x_2838_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
lean_dec(v_a_2834_);
lean_dec(v_val_2832_);
v___x_2841_ = lean_box(v___x_2840_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2841_);
v___x_2843_ = v___x_2836_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
else
{
if (v___x_2840_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
lean_dec(v_a_2834_);
lean_dec(v_val_2832_);
v___x_2845_ = lean_box(v___x_2840_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2845_);
v___x_2847_ = v___x_2836_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
else
{
size_t v___x_2849_; size_t v___x_2850_; uint64_t v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = lean_usize_of_nat(v___x_2839_);
v___x_2851_ = lean_unbox_uint64(v_a_2834_);
lean_dec(v_a_2834_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2851_, v_val_2832_, v___x_2849_, v___x_2850_);
lean_dec(v_val_2832_);
v___x_2853_ = lean_box(v___x_2852_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2853_);
v___x_2855_ = v___x_2836_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_val_2832_);
v_a_2858_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2833_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2833_);
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
else
{
uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
lean_dec(v_a_2828_);
v___x_2866_ = 1;
v___x_2867_ = lean_box(v___x_2866_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2867_);
v___x_2869_ = v___x_2830_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
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
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2827_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2827_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_c_2880_);
return v_res_2891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2895_, lean_object* v_c_x3f_2896_, lean_object* v_cs_x27_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
if (lean_obj_tag(v_cs_2895_) == 0)
{
lean_object* v___x_2909_; lean_object* v_toGoalState_2910_; lean_object* v_split_2911_; lean_object* v_mvarId_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3027_; 
v___x_2909_ = lean_st_ref_take(v_a_2898_);
v_toGoalState_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc_ref(v_toGoalState_2910_);
v_split_2911_ = lean_ctor_get(v_toGoalState_2910_, 15);
lean_inc_ref(v_split_2911_);
v_mvarId_2912_ = lean_ctor_get(v___x_2909_, 1);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v___x_2909_, 0);
lean_dec(v_unused_3028_);
v___x_2914_ = v___x_2909_;
v_isShared_2915_ = v_isSharedCheck_3027_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_mvarId_2912_);
lean_dec(v___x_2909_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3027_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v_nextDeclIdx_2916_; lean_object* v_enodeMap_2917_; lean_object* v_exprs_2918_; lean_object* v_parents_2919_; lean_object* v_congrTable_2920_; lean_object* v_appMap_2921_; lean_object* v_indicesFound_2922_; lean_object* v_toProcess_2923_; lean_object* v_internalizing_2924_; uint8_t v_inconsistent_2925_; lean_object* v_nextIdx_2926_; lean_object* v_newRawFacts_2927_; lean_object* v_facts_2928_; lean_object* v_extThms_2929_; lean_object* v_ematch_2930_; lean_object* v_inj_2931_; lean_object* v_clean_2932_; lean_object* v_sstates_2933_; lean_object* v_goalStack_2934_; uint64_t v_introBase_2935_; lean_object* v_numIntros_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_3025_; 
v_nextDeclIdx_2916_ = lean_ctor_get(v_toGoalState_2910_, 0);
v_enodeMap_2917_ = lean_ctor_get(v_toGoalState_2910_, 1);
v_exprs_2918_ = lean_ctor_get(v_toGoalState_2910_, 2);
v_parents_2919_ = lean_ctor_get(v_toGoalState_2910_, 3);
v_congrTable_2920_ = lean_ctor_get(v_toGoalState_2910_, 4);
v_appMap_2921_ = lean_ctor_get(v_toGoalState_2910_, 5);
v_indicesFound_2922_ = lean_ctor_get(v_toGoalState_2910_, 6);
v_toProcess_2923_ = lean_ctor_get(v_toGoalState_2910_, 7);
v_internalizing_2924_ = lean_ctor_get(v_toGoalState_2910_, 8);
v_inconsistent_2925_ = lean_ctor_get_uint8(v_toGoalState_2910_, sizeof(void*)*20 + 8);
v_nextIdx_2926_ = lean_ctor_get(v_toGoalState_2910_, 9);
v_newRawFacts_2927_ = lean_ctor_get(v_toGoalState_2910_, 10);
v_facts_2928_ = lean_ctor_get(v_toGoalState_2910_, 11);
v_extThms_2929_ = lean_ctor_get(v_toGoalState_2910_, 12);
v_ematch_2930_ = lean_ctor_get(v_toGoalState_2910_, 13);
v_inj_2931_ = lean_ctor_get(v_toGoalState_2910_, 14);
v_clean_2932_ = lean_ctor_get(v_toGoalState_2910_, 16);
v_sstates_2933_ = lean_ctor_get(v_toGoalState_2910_, 17);
v_goalStack_2934_ = lean_ctor_get(v_toGoalState_2910_, 18);
v_introBase_2935_ = lean_ctor_get_uint64(v_toGoalState_2910_, sizeof(void*)*20);
v_numIntros_2936_ = lean_ctor_get(v_toGoalState_2910_, 19);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_toGoalState_2910_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_toGoalState_2910_, 15);
lean_dec(v_unused_3026_);
v___x_2938_ = v_toGoalState_2910_;
v_isShared_2939_ = v_isSharedCheck_3025_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_numIntros_2936_);
lean_inc(v_goalStack_2934_);
lean_inc(v_sstates_2933_);
lean_inc(v_clean_2932_);
lean_inc(v_inj_2931_);
lean_inc(v_ematch_2930_);
lean_inc(v_extThms_2929_);
lean_inc(v_facts_2928_);
lean_inc(v_newRawFacts_2927_);
lean_inc(v_nextIdx_2926_);
lean_inc(v_internalizing_2924_);
lean_inc(v_toProcess_2923_);
lean_inc(v_indicesFound_2922_);
lean_inc(v_appMap_2921_);
lean_inc(v_congrTable_2920_);
lean_inc(v_parents_2919_);
lean_inc(v_exprs_2918_);
lean_inc(v_enodeMap_2917_);
lean_inc(v_nextDeclIdx_2916_);
lean_dec(v_toGoalState_2910_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_3025_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v_added_2940_; lean_object* v_resolved_2941_; lean_object* v_trace_2942_; lean_object* v_lookaheads_2943_; lean_object* v_argPosMap_2944_; lean_object* v_argsAt_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3023_; 
v_added_2940_ = lean_ctor_get(v_split_2911_, 1);
v_resolved_2941_ = lean_ctor_get(v_split_2911_, 2);
v_trace_2942_ = lean_ctor_get(v_split_2911_, 3);
v_lookaheads_2943_ = lean_ctor_get(v_split_2911_, 4);
v_argPosMap_2944_ = lean_ctor_get(v_split_2911_, 5);
v_argsAt_2945_ = lean_ctor_get(v_split_2911_, 6);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_split_2911_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v_split_2911_, 0);
lean_dec(v_unused_3024_);
v___x_2947_ = v_split_2911_;
v_isShared_2948_ = v_isSharedCheck_3023_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_argsAt_2945_);
lean_inc(v_argPosMap_2944_);
lean_inc(v_lookaheads_2943_);
lean_inc(v_trace_2942_);
lean_inc(v_resolved_2941_);
lean_inc(v_added_2940_);
lean_dec(v_split_2911_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3023_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_List_reverse___redArg(v_cs_x27_2897_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_added_2940_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_resolved_2941_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_trace_2942_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_lookaheads_2943_);
lean_ctor_set(v_reuseFailAlloc_3022_, 5, v_argPosMap_2944_);
lean_ctor_set(v_reuseFailAlloc_3022_, 6, v_argsAt_2945_);
v___x_2951_ = v_reuseFailAlloc_3022_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 15, v___x_2951_);
v___x_2953_ = v___x_2938_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_nextDeclIdx_2916_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_enodeMap_2917_);
lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_exprs_2918_);
lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_parents_2919_);
lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_congrTable_2920_);
lean_ctor_set(v_reuseFailAlloc_3021_, 5, v_appMap_2921_);
lean_ctor_set(v_reuseFailAlloc_3021_, 6, v_indicesFound_2922_);
lean_ctor_set(v_reuseFailAlloc_3021_, 7, v_toProcess_2923_);
lean_ctor_set(v_reuseFailAlloc_3021_, 8, v_internalizing_2924_);
lean_ctor_set(v_reuseFailAlloc_3021_, 9, v_nextIdx_2926_);
lean_ctor_set(v_reuseFailAlloc_3021_, 10, v_newRawFacts_2927_);
lean_ctor_set(v_reuseFailAlloc_3021_, 11, v_facts_2928_);
lean_ctor_set(v_reuseFailAlloc_3021_, 12, v_extThms_2929_);
lean_ctor_set(v_reuseFailAlloc_3021_, 13, v_ematch_2930_);
lean_ctor_set(v_reuseFailAlloc_3021_, 14, v_inj_2931_);
lean_ctor_set(v_reuseFailAlloc_3021_, 15, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_3021_, 16, v_clean_2932_);
lean_ctor_set(v_reuseFailAlloc_3021_, 17, v_sstates_2933_);
lean_ctor_set(v_reuseFailAlloc_3021_, 18, v_goalStack_2934_);
lean_ctor_set(v_reuseFailAlloc_3021_, 19, v_numIntros_2936_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, sizeof(void*)*20 + 8, v_inconsistent_2925_);
lean_ctor_set_uint64(v_reuseFailAlloc_3021_, sizeof(void*)*20, v_introBase_2935_);
v___x_2953_ = v_reuseFailAlloc_3021_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2955_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2953_);
v___x_2955_ = v___x_2914_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_mvarId_2912_);
v___x_2955_ = v_reuseFailAlloc_3020_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_st_ref_put(v_a_2898_, v___x_2955_);
if (lean_obj_tag(v_c_x3f_2896_) == 1)
{
lean_object* v___x_2957_; lean_object* v_toGoalState_2958_; lean_object* v_ematch_2959_; lean_object* v_mvarId_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3017_; 
v___x_2957_ = lean_st_ref_take(v_a_2898_);
v_toGoalState_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc_ref(v_toGoalState_2958_);
v_ematch_2959_ = lean_ctor_get(v_toGoalState_2958_, 13);
lean_inc_ref(v_ematch_2959_);
v_mvarId_2960_ = lean_ctor_get(v___x_2957_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_2957_, 0);
lean_dec(v_unused_3018_);
v___x_2962_ = v___x_2957_;
v_isShared_2963_ = v_isSharedCheck_3017_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_mvarId_2960_);
lean_dec(v___x_2957_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3017_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_nextDeclIdx_2964_; lean_object* v_enodeMap_2965_; lean_object* v_exprs_2966_; lean_object* v_parents_2967_; lean_object* v_congrTable_2968_; lean_object* v_appMap_2969_; lean_object* v_indicesFound_2970_; lean_object* v_toProcess_2971_; lean_object* v_internalizing_2972_; uint8_t v_inconsistent_2973_; lean_object* v_nextIdx_2974_; lean_object* v_newRawFacts_2975_; lean_object* v_facts_2976_; lean_object* v_extThms_2977_; lean_object* v_inj_2978_; lean_object* v_split_2979_; lean_object* v_clean_2980_; lean_object* v_sstates_2981_; lean_object* v_goalStack_2982_; uint64_t v_introBase_2983_; lean_object* v_numIntros_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3015_; 
v_nextDeclIdx_2964_ = lean_ctor_get(v_toGoalState_2958_, 0);
v_enodeMap_2965_ = lean_ctor_get(v_toGoalState_2958_, 1);
v_exprs_2966_ = lean_ctor_get(v_toGoalState_2958_, 2);
v_parents_2967_ = lean_ctor_get(v_toGoalState_2958_, 3);
v_congrTable_2968_ = lean_ctor_get(v_toGoalState_2958_, 4);
v_appMap_2969_ = lean_ctor_get(v_toGoalState_2958_, 5);
v_indicesFound_2970_ = lean_ctor_get(v_toGoalState_2958_, 6);
v_toProcess_2971_ = lean_ctor_get(v_toGoalState_2958_, 7);
v_internalizing_2972_ = lean_ctor_get(v_toGoalState_2958_, 8);
v_inconsistent_2973_ = lean_ctor_get_uint8(v_toGoalState_2958_, sizeof(void*)*20 + 8);
v_nextIdx_2974_ = lean_ctor_get(v_toGoalState_2958_, 9);
v_newRawFacts_2975_ = lean_ctor_get(v_toGoalState_2958_, 10);
v_facts_2976_ = lean_ctor_get(v_toGoalState_2958_, 11);
v_extThms_2977_ = lean_ctor_get(v_toGoalState_2958_, 12);
v_inj_2978_ = lean_ctor_get(v_toGoalState_2958_, 14);
v_split_2979_ = lean_ctor_get(v_toGoalState_2958_, 15);
v_clean_2980_ = lean_ctor_get(v_toGoalState_2958_, 16);
v_sstates_2981_ = lean_ctor_get(v_toGoalState_2958_, 17);
v_goalStack_2982_ = lean_ctor_get(v_toGoalState_2958_, 18);
v_introBase_2983_ = lean_ctor_get_uint64(v_toGoalState_2958_, sizeof(void*)*20);
v_numIntros_2984_ = lean_ctor_get(v_toGoalState_2958_, 19);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_toGoalState_2958_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v_toGoalState_2958_, 13);
lean_dec(v_unused_3016_);
v___x_2986_ = v_toGoalState_2958_;
v_isShared_2987_ = v_isSharedCheck_3015_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_numIntros_2984_);
lean_inc(v_goalStack_2982_);
lean_inc(v_sstates_2981_);
lean_inc(v_clean_2980_);
lean_inc(v_split_2979_);
lean_inc(v_inj_2978_);
lean_inc(v_extThms_2977_);
lean_inc(v_facts_2976_);
lean_inc(v_newRawFacts_2975_);
lean_inc(v_nextIdx_2974_);
lean_inc(v_internalizing_2972_);
lean_inc(v_toProcess_2971_);
lean_inc(v_indicesFound_2970_);
lean_inc(v_appMap_2969_);
lean_inc(v_congrTable_2968_);
lean_inc(v_parents_2967_);
lean_inc(v_exprs_2966_);
lean_inc(v_enodeMap_2965_);
lean_inc(v_nextDeclIdx_2964_);
lean_dec(v_toGoalState_2958_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3015_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v_thmMap_2988_; lean_object* v_gmt_2989_; lean_object* v_thms_2990_; lean_object* v_newThms_2991_; lean_object* v_numInstances_2992_; lean_object* v_numDelayedInstances_2993_; lean_object* v_preInstances_2994_; lean_object* v_nextThmIdx_2995_; lean_object* v_matchEqNames_2996_; lean_object* v_delayedThmInsts_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3013_; 
v_thmMap_2988_ = lean_ctor_get(v_ematch_2959_, 0);
v_gmt_2989_ = lean_ctor_get(v_ematch_2959_, 1);
v_thms_2990_ = lean_ctor_get(v_ematch_2959_, 2);
v_newThms_2991_ = lean_ctor_get(v_ematch_2959_, 3);
v_numInstances_2992_ = lean_ctor_get(v_ematch_2959_, 4);
v_numDelayedInstances_2993_ = lean_ctor_get(v_ematch_2959_, 5);
v_preInstances_2994_ = lean_ctor_get(v_ematch_2959_, 7);
v_nextThmIdx_2995_ = lean_ctor_get(v_ematch_2959_, 8);
v_matchEqNames_2996_ = lean_ctor_get(v_ematch_2959_, 9);
v_delayedThmInsts_2997_ = lean_ctor_get(v_ematch_2959_, 10);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_ematch_2959_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v_ematch_2959_, 6);
lean_dec(v_unused_3014_);
v___x_2999_ = v_ematch_2959_;
v_isShared_3000_ = v_isSharedCheck_3013_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_delayedThmInsts_2997_);
lean_inc(v_matchEqNames_2996_);
lean_inc(v_nextThmIdx_2995_);
lean_inc(v_preInstances_2994_);
lean_inc(v_numDelayedInstances_2993_);
lean_inc(v_numInstances_2992_);
lean_inc(v_newThms_2991_);
lean_inc(v_thms_2990_);
lean_inc(v_gmt_2989_);
lean_inc(v_thmMap_2988_);
lean_dec(v_ematch_2959_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3013_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 6, v___x_3001_);
v___x_3003_ = v___x_2999_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_thmMap_2988_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_gmt_2989_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_thms_2990_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_newThms_2991_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_numInstances_2992_);
lean_ctor_set(v_reuseFailAlloc_3012_, 5, v_numDelayedInstances_2993_);
lean_ctor_set(v_reuseFailAlloc_3012_, 6, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3012_, 7, v_preInstances_2994_);
lean_ctor_set(v_reuseFailAlloc_3012_, 8, v_nextThmIdx_2995_);
lean_ctor_set(v_reuseFailAlloc_3012_, 9, v_matchEqNames_2996_);
lean_ctor_set(v_reuseFailAlloc_3012_, 10, v_delayedThmInsts_2997_);
v___x_3003_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 13, v___x_3003_);
v___x_3005_ = v___x_2986_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_nextDeclIdx_2964_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_enodeMap_2965_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_exprs_2966_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_parents_2967_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_congrTable_2968_);
lean_ctor_set(v_reuseFailAlloc_3011_, 5, v_appMap_2969_);
lean_ctor_set(v_reuseFailAlloc_3011_, 6, v_indicesFound_2970_);
lean_ctor_set(v_reuseFailAlloc_3011_, 7, v_toProcess_2971_);
lean_ctor_set(v_reuseFailAlloc_3011_, 8, v_internalizing_2972_);
lean_ctor_set(v_reuseFailAlloc_3011_, 9, v_nextIdx_2974_);
lean_ctor_set(v_reuseFailAlloc_3011_, 10, v_newRawFacts_2975_);
lean_ctor_set(v_reuseFailAlloc_3011_, 11, v_facts_2976_);
lean_ctor_set(v_reuseFailAlloc_3011_, 12, v_extThms_2977_);
lean_ctor_set(v_reuseFailAlloc_3011_, 13, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3011_, 14, v_inj_2978_);
lean_ctor_set(v_reuseFailAlloc_3011_, 15, v_split_2979_);
lean_ctor_set(v_reuseFailAlloc_3011_, 16, v_clean_2980_);
lean_ctor_set(v_reuseFailAlloc_3011_, 17, v_sstates_2981_);
lean_ctor_set(v_reuseFailAlloc_3011_, 18, v_goalStack_2982_);
lean_ctor_set(v_reuseFailAlloc_3011_, 19, v_numIntros_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3011_, sizeof(void*)*20 + 8, v_inconsistent_2973_);
lean_ctor_set_uint64(v_reuseFailAlloc_3011_, sizeof(void*)*20, v_introBase_2983_);
v___x_3005_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_3005_);
v___x_3007_ = v___x_2962_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_mvarId_2960_);
v___x_3007_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_st_ref_put(v_a_2898_, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_c_x3f_2896_);
return v___x_3009_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_c_x3f_2896_);
return v___x_3019_;
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
lean_object* v_head_3029_; lean_object* v_tail_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3250_; 
v_head_3029_ = lean_ctor_get(v_cs_2895_, 0);
v_tail_3030_ = lean_ctor_get(v_cs_2895_, 1);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_cs_2895_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3032_ = v_cs_2895_;
v_isShared_3033_ = v_isSharedCheck_3250_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_tail_3030_);
lean_inc(v_head_3029_);
lean_dec(v_cs_2895_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3250_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; uint8_t v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; uint8_t v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; uint8_t v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; uint8_t v___y_3139_; lean_object* v___x_3142_; 
v___x_3142_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_3029_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; uint8_t v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = lean_unbox(v_a_3143_);
lean_dec(v_a_3143_);
if (v___x_3144_ == 0)
{
lean_del_object(v___x_3032_);
lean_dec(v_head_3029_);
v_cs_2895_ = v_tail_3030_;
goto _start;
}
else
{
lean_object* v_toCold_3146_; lean_object* v_options_3147_; lean_object* v_inheritedTraceOptions_3148_; uint8_t v_hasTrace_3149_; uint8_t v___x_3150_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; uint8_t v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; uint8_t v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v___y_3165_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; 
v_toCold_3146_ = lean_ctor_get(v_a_2906_, 0);
v_options_3147_ = lean_ctor_get(v_toCold_3146_, 2);
v_inheritedTraceOptions_3148_ = lean_ctor_get(v_toCold_3146_, 11);
v_hasTrace_3149_ = lean_ctor_get_uint8(v_options_3147_, sizeof(void*)*1);
v___x_3150_ = 0;
if (v_hasTrace_3149_ == 0)
{
v___y_3176_ = v_a_2898_;
v___y_3177_ = v_a_2899_;
v___y_3178_ = v_a_2900_;
v___y_3179_ = v_a_2901_;
v___y_3180_ = v_a_2902_;
v___y_3181_ = v_a_2903_;
v___y_3182_ = v_a_2904_;
v___y_3183_ = v_a_2905_;
v___y_3184_ = v_a_2906_;
v___y_3185_ = v_a_2907_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3219_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3148_, v_options_3147_, v___x_3218_);
if (v___x_3219_ == 0)
{
v___y_3176_ = v_a_2898_;
v___y_3177_ = v_a_2899_;
v___y_3178_ = v_a_2900_;
v___y_3179_ = v_a_2901_;
v___y_3180_ = v_a_2902_;
v___y_3181_ = v_a_2903_;
v___y_3182_ = v_a_2904_;
v___y_3183_ = v_a_2905_;
v___y_3184_ = v_a_2906_;
v___y_3185_ = v_a_2907_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_Meta_Grind_updateLastTag(v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec_ref_known(v___x_3220_, 1);
v___x_3221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3222_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_3029_);
v___x_3223_ = l_Lean_MessageData_ofExpr(v___x_3222_);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3221_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3217_, v___x_3224_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_dec_ref_known(v___x_3225_, 1);
v___y_3176_ = v_a_2898_;
v___y_3177_ = v_a_2899_;
v___y_3178_ = v_a_2900_;
v___y_3179_ = v_a_2901_;
v___y_3180_ = v_a_2902_;
v___y_3181_ = v_a_2903_;
v___y_3182_ = v_a_2904_;
v___y_3183_ = v_a_2905_;
v___y_3184_ = v_a_2906_;
v___y_3185_ = v_a_2907_;
goto v___jp_3175_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3234_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3220_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3220_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
v___jp_3151_:
{
if (lean_obj_tag(v_c_x3f_2896_) == 0)
{
lean_object* v___x_3166_; 
lean_del_object(v___x_3032_);
v___x_3166_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3166_, 0, v_head_3029_);
lean_ctor_set(v___x_3166_, 1, v___y_3156_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*2, v___y_3155_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*2 + 1, v___y_3159_);
v_cs_2895_ = v_tail_3030_;
v_c_x3f_2896_ = v___x_3166_;
v_a_2898_ = v___y_3161_;
v_a_2899_ = v___y_3162_;
v_a_2900_ = v___y_3157_;
v_a_2901_ = v___y_3152_;
v_a_2902_ = v___y_3153_;
v_a_2903_ = v___y_3158_;
v_a_2904_ = v___y_3154_;
v_a_2905_ = v___y_3160_;
v_a_2906_ = v___y_3163_;
v_a_2907_ = v___y_3164_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3168_; 
v_tryPostpone_3168_ = lean_ctor_get_uint8(v_c_x3f_2896_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3168_ == 0)
{
if (v___y_3159_ == 0)
{
lean_object* v_c_3169_; lean_object* v_numCases_3170_; 
v_c_3169_ = lean_ctor_get(v_c_x3f_2896_, 0);
v_numCases_3170_ = lean_ctor_get(v_c_x3f_2896_, 1);
lean_inc(v_numCases_3170_);
lean_inc_ref(v_c_3169_);
v___y_3124_ = v___y_3153_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3156_;
v___y_3129_ = v___y_3158_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v_c_3169_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v_numCases_3170_;
v___y_3134_ = v___y_3160_;
v___y_3135_ = v___y_3162_;
v___y_3136_ = v___y_3161_;
v___y_3137_ = v___y_3164_;
v___y_3138_ = v___y_3163_;
v___y_3139_ = v___x_3150_;
goto v___jp_3123_;
}
else
{
lean_dec(v___y_3156_);
v___y_3035_ = v___y_3158_;
v___y_3036_ = v___y_3157_;
v___y_3037_ = v___y_3153_;
v___y_3038_ = v___y_3152_;
v___y_3039_ = v___y_3154_;
v___y_3040_ = v___y_3160_;
v___y_3041_ = v___y_3162_;
v___y_3042_ = v___y_3161_;
v___y_3043_ = v___y_3164_;
v___y_3044_ = v___y_3163_;
goto v___jp_3034_;
}
}
else
{
if (v___y_3159_ == 0)
{
lean_object* v_c_3171_; 
lean_del_object(v___x_3032_);
v_c_3171_ = lean_ctor_get(v_c_x3f_2896_, 0);
lean_inc_ref(v_c_3171_);
lean_dec_ref_known(v_c_x3f_2896_, 2);
v___y_3050_ = v___y_3152_;
v___y_3051_ = v___y_3153_;
v___y_3052_ = v___y_3154_;
v___y_3053_ = v___y_3155_;
v___y_3054_ = v___y_3156_;
v___y_3055_ = v___y_3157_;
v___y_3056_ = v___y_3158_;
v___y_3057_ = v_c_3171_;
v___y_3058_ = v___y_3159_;
v___y_3059_ = v___y_3160_;
v___y_3060_ = v___y_3161_;
v___y_3061_ = v___y_3162_;
v___y_3062_ = v___y_3164_;
v___y_3063_ = v___y_3163_;
goto v___jp_3049_;
}
else
{
if (v___y_3165_ == 0)
{
lean_object* v_c_3172_; lean_object* v_numCases_3173_; 
v_c_3172_ = lean_ctor_get(v_c_x3f_2896_, 0);
v_numCases_3173_ = lean_ctor_get(v_c_x3f_2896_, 1);
lean_inc(v_numCases_3173_);
lean_inc_ref(v_c_3172_);
v___y_3124_ = v___y_3153_;
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3156_;
v___y_3129_ = v___y_3158_;
v___y_3130_ = v___y_3157_;
v___y_3131_ = v_c_3172_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v_numCases_3173_;
v___y_3134_ = v___y_3160_;
v___y_3135_ = v___y_3162_;
v___y_3136_ = v___y_3161_;
v___y_3137_ = v___y_3164_;
v___y_3138_ = v___y_3163_;
v___y_3139_ = v___y_3165_;
goto v___jp_3123_;
}
else
{
lean_object* v_c_3174_; 
lean_del_object(v___x_3032_);
v_c_3174_ = lean_ctor_get(v_c_x3f_2896_, 0);
lean_inc_ref(v_c_3174_);
lean_dec_ref_known(v_c_x3f_2896_, 2);
v___y_3050_ = v___y_3152_;
v___y_3051_ = v___y_3153_;
v___y_3052_ = v___y_3154_;
v___y_3053_ = v___y_3155_;
v___y_3054_ = v___y_3156_;
v___y_3055_ = v___y_3157_;
v___y_3056_ = v___y_3158_;
v___y_3057_ = v_c_3174_;
v___y_3058_ = v___y_3159_;
v___y_3059_ = v___y_3160_;
v___y_3060_ = v___y_3161_;
v___y_3061_ = v___y_3162_;
v___y_3062_ = v___y_3164_;
v___y_3063_ = v___y_3163_;
goto v___jp_3049_;
}
}
}
}
}
v___jp_3175_:
{
lean_object* v___x_3186_; 
lean_inc(v_head_3029_);
v___x_3186_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_3029_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3186_, 1);
switch(lean_obj_tag(v_a_3187_))
{
case 0:
{
lean_del_object(v___x_3032_);
lean_dec(v_head_3029_);
v_cs_2895_ = v_tail_3030_;
v_a_2898_ = v___y_3176_;
v_a_2899_ = v___y_3177_;
v_a_2900_ = v___y_3178_;
v_a_2901_ = v___y_3179_;
v_a_2902_ = v___y_3180_;
v_a_2903_ = v___y_3181_;
v_a_2904_ = v___y_3182_;
v_a_2905_ = v___y_3183_;
v_a_2906_ = v___y_3184_;
v_a_2907_ = v___y_3185_;
goto _start;
}
case 1:
{
lean_object* v___x_3189_; 
lean_del_object(v___x_3032_);
v___x_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_head_3029_);
lean_ctor_set(v___x_3189_, 1, v_cs_x27_2897_);
v_cs_2895_ = v_tail_3030_;
v_cs_x27_2897_ = v___x_3189_;
v_a_2898_ = v___y_3176_;
v_a_2899_ = v___y_3177_;
v_a_2900_ = v___y_3178_;
v_a_2901_ = v___y_3179_;
v_a_2902_ = v___y_3180_;
v_a_2903_ = v___y_3181_;
v_a_2904_ = v___y_3182_;
v_a_2905_ = v___y_3183_;
v_a_2906_ = v___y_3184_;
v_a_2907_ = v___y_3185_;
goto _start;
}
default: 
{
lean_object* v_numCases_3191_; uint8_t v_isRec_3192_; uint8_t v_tryPostpone_3193_; lean_object* v___x_3194_; 
v_numCases_3191_ = lean_ctor_get(v_a_3187_, 0);
lean_inc(v_numCases_3191_);
v_isRec_3192_ = lean_ctor_get_uint8(v_a_3187_, sizeof(void*)*1);
v_tryPostpone_3193_ = lean_ctor_get_uint8(v_a_3187_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3187_, 1);
v___x_3194_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3178_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; uint8_t v___x_3196_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = lean_unbox(v_a_3195_);
lean_dec(v_a_3195_);
if (v___x_3196_ == 0)
{
v___y_3152_ = v___y_3179_;
v___y_3153_ = v___y_3180_;
v___y_3154_ = v___y_3182_;
v___y_3155_ = v_isRec_3192_;
v___y_3156_ = v_numCases_3191_;
v___y_3157_ = v___y_3178_;
v___y_3158_ = v___y_3181_;
v___y_3159_ = v_tryPostpone_3193_;
v___y_3160_ = v___y_3183_;
v___y_3161_ = v___y_3176_;
v___y_3162_ = v___y_3177_;
v___y_3163_ = v___y_3184_;
v___y_3164_ = v___y_3185_;
v___y_3165_ = v___x_3150_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = lean_unsigned_to_nat(1u);
v___x_3198_ = lean_nat_dec_lt(v___x_3197_, v_numCases_3191_);
if (v___x_3198_ == 0)
{
v___y_3152_ = v___y_3179_;
v___y_3153_ = v___y_3180_;
v___y_3154_ = v___y_3182_;
v___y_3155_ = v_isRec_3192_;
v___y_3156_ = v_numCases_3191_;
v___y_3157_ = v___y_3178_;
v___y_3158_ = v___y_3181_;
v___y_3159_ = v_tryPostpone_3193_;
v___y_3160_ = v___y_3183_;
v___y_3161_ = v___y_3176_;
v___y_3162_ = v___y_3177_;
v___y_3163_ = v___y_3184_;
v___y_3164_ = v___y_3185_;
v___y_3165_ = v___x_3198_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3199_; 
lean_dec(v_numCases_3191_);
lean_del_object(v___x_3032_);
v___x_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_head_3029_);
lean_ctor_set(v___x_3199_, 1, v_cs_x27_2897_);
v_cs_2895_ = v_tail_3030_;
v_cs_x27_2897_ = v___x_3199_;
v_a_2898_ = v___y_3176_;
v_a_2899_ = v___y_3177_;
v_a_2900_ = v___y_3178_;
v_a_2901_ = v___y_3179_;
v_a_2902_ = v___y_3180_;
v_a_2903_ = v___y_3181_;
v_a_2904_ = v___y_3182_;
v_a_2905_ = v___y_3183_;
v_a_2906_ = v___y_3184_;
v_a_2907_ = v___y_3185_;
goto _start;
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_numCases_3191_);
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3201_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3194_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3194_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3209_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3186_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3186_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3242_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3142_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3142_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
v___jp_3034_:
{
lean_object* v___x_3046_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v_cs_x27_2897_);
v___x_3046_ = v___x_3032_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_head_3029_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_cs_x27_2897_);
v___x_3046_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
v_cs_2895_ = v_tail_3030_;
v_cs_x27_2897_ = v___x_3046_;
v_a_2898_ = v___y_3042_;
v_a_2899_ = v___y_3041_;
v_a_2900_ = v___y_3036_;
v_a_2901_ = v___y_3038_;
v_a_2902_ = v___y_3037_;
v_a_2903_ = v___y_3035_;
v_a_2904_ = v___y_3039_;
v_a_2905_ = v___y_3040_;
v_a_2906_ = v___y_3044_;
v_a_2907_ = v___y_3043_;
goto _start;
}
}
v___jp_3049_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3064_, 0, v_head_3029_);
lean_ctor_set(v___x_3064_, 1, v___y_3054_);
lean_ctor_set_uint8(v___x_3064_, sizeof(void*)*2, v___y_3053_);
lean_ctor_set_uint8(v___x_3064_, sizeof(void*)*2 + 1, v___y_3058_);
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___y_3057_);
lean_ctor_set(v___x_3065_, 1, v_cs_x27_2897_);
v_cs_2895_ = v_tail_3030_;
v_c_x3f_2896_ = v___x_3064_;
v_cs_x27_2897_ = v___x_3065_;
v_a_2898_ = v___y_3060_;
v_a_2899_ = v___y_3061_;
v_a_2900_ = v___y_3055_;
v_a_2901_ = v___y_3050_;
v_a_2902_ = v___y_3051_;
v_a_2903_ = v___y_3056_;
v_a_2904_ = v___y_3052_;
v_a_2905_ = v___y_3059_;
v_a_2906_ = v___y_3063_;
v_a_2907_ = v___y_3062_;
goto _start;
}
v___jp_3067_:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_3029_, v___y_3079_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3075_, v___y_3079_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; uint8_t v___x_3087_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
v___x_3087_ = lean_nat_dec_lt(v_a_3084_, v_a_3086_);
lean_dec(v_a_3086_);
lean_dec(v_a_3084_);
if (v___x_3087_ == 0)
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_nat_dec_lt(v___y_3072_, v___y_3077_);
lean_dec(v___y_3077_);
if (v___x_3088_ == 0)
{
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3072_);
v___y_3035_ = v___y_3073_;
v___y_3036_ = v___y_3074_;
v___y_3037_ = v___y_3068_;
v___y_3038_ = v___y_3069_;
v___y_3039_ = v___y_3070_;
v___y_3040_ = v___y_3078_;
v___y_3041_ = v___y_3080_;
v___y_3042_ = v___y_3079_;
v___y_3043_ = v___y_3082_;
v___y_3044_ = v___y_3081_;
goto v___jp_3034_;
}
else
{
lean_del_object(v___x_3032_);
lean_dec(v_c_x3f_2896_);
v___y_3050_ = v___y_3069_;
v___y_3051_ = v___y_3068_;
v___y_3052_ = v___y_3070_;
v___y_3053_ = v___y_3071_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3074_;
v___y_3056_ = v___y_3073_;
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3076_;
v___y_3059_ = v___y_3078_;
v___y_3060_ = v___y_3079_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3082_;
v___y_3063_ = v___y_3081_;
goto v___jp_3049_;
}
}
else
{
lean_dec(v___y_3077_);
lean_del_object(v___x_3032_);
lean_dec(v_c_x3f_2896_);
v___y_3050_ = v___y_3069_;
v___y_3051_ = v___y_3068_;
v___y_3052_ = v___y_3070_;
v___y_3053_ = v___y_3071_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3074_;
v___y_3056_ = v___y_3073_;
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3076_;
v___y_3059_ = v___y_3078_;
v___y_3060_ = v___y_3079_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3082_;
v___y_3063_ = v___y_3081_;
goto v___jp_3049_;
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_a_3084_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3072_);
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3089_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3085_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3085_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3072_);
lean_del_object(v___x_3032_);
lean_dec(v_tail_3030_);
lean_dec(v_head_3029_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3097_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3083_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3083_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
v___jp_3105_:
{
lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = lean_unsigned_to_nat(1u);
v___x_3122_ = lean_nat_dec_lt(v___x_3121_, v___y_3115_);
if (v___x_3122_ == 0)
{
v___y_3068_ = v___y_3106_;
v___y_3069_ = v___y_3107_;
v___y_3070_ = v___y_3108_;
v___y_3071_ = v___y_3109_;
v___y_3072_ = v___y_3110_;
v___y_3073_ = v___y_3111_;
v___y_3074_ = v___y_3112_;
v___y_3075_ = v___y_3113_;
v___y_3076_ = v___y_3114_;
v___y_3077_ = v___y_3115_;
v___y_3078_ = v___y_3116_;
v___y_3079_ = v___y_3118_;
v___y_3080_ = v___y_3117_;
v___y_3081_ = v___y_3120_;
v___y_3082_ = v___y_3119_;
goto v___jp_3067_;
}
else
{
lean_dec(v___y_3115_);
lean_del_object(v___x_3032_);
lean_dec(v_c_x3f_2896_);
v___y_3050_ = v___y_3107_;
v___y_3051_ = v___y_3106_;
v___y_3052_ = v___y_3108_;
v___y_3053_ = v___y_3109_;
v___y_3054_ = v___y_3110_;
v___y_3055_ = v___y_3112_;
v___y_3056_ = v___y_3111_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3114_;
v___y_3059_ = v___y_3116_;
v___y_3060_ = v___y_3118_;
v___y_3061_ = v___y_3117_;
v___y_3062_ = v___y_3119_;
v___y_3063_ = v___y_3120_;
goto v___jp_3049_;
}
}
v___jp_3123_:
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = lean_unsigned_to_nat(1u);
v___x_3141_ = lean_nat_dec_eq(v___y_3128_, v___x_3140_);
if (v___x_3141_ == 0)
{
v___y_3068_ = v___y_3124_;
v___y_3069_ = v___y_3125_;
v___y_3070_ = v___y_3126_;
v___y_3071_ = v___y_3127_;
v___y_3072_ = v___y_3128_;
v___y_3073_ = v___y_3129_;
v___y_3074_ = v___y_3130_;
v___y_3075_ = v___y_3131_;
v___y_3076_ = v___y_3132_;
v___y_3077_ = v___y_3133_;
v___y_3078_ = v___y_3134_;
v___y_3079_ = v___y_3136_;
v___y_3080_ = v___y_3135_;
v___y_3081_ = v___y_3138_;
v___y_3082_ = v___y_3137_;
goto v___jp_3067_;
}
else
{
if (v___y_3127_ == 0)
{
v___y_3106_ = v___y_3124_;
v___y_3107_ = v___y_3125_;
v___y_3108_ = v___y_3126_;
v___y_3109_ = v___y_3127_;
v___y_3110_ = v___y_3128_;
v___y_3111_ = v___y_3129_;
v___y_3112_ = v___y_3130_;
v___y_3113_ = v___y_3131_;
v___y_3114_ = v___y_3132_;
v___y_3115_ = v___y_3133_;
v___y_3116_ = v___y_3134_;
v___y_3117_ = v___y_3135_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
goto v___jp_3105_;
}
else
{
if (v___y_3139_ == 0)
{
v___y_3068_ = v___y_3124_;
v___y_3069_ = v___y_3125_;
v___y_3070_ = v___y_3126_;
v___y_3071_ = v___y_3127_;
v___y_3072_ = v___y_3128_;
v___y_3073_ = v___y_3129_;
v___y_3074_ = v___y_3130_;
v___y_3075_ = v___y_3131_;
v___y_3076_ = v___y_3132_;
v___y_3077_ = v___y_3133_;
v___y_3078_ = v___y_3134_;
v___y_3079_ = v___y_3136_;
v___y_3080_ = v___y_3135_;
v___y_3081_ = v___y_3138_;
v___y_3082_ = v___y_3137_;
goto v___jp_3067_;
}
else
{
v___y_3106_ = v___y_3124_;
v___y_3107_ = v___y_3125_;
v___y_3108_ = v___y_3126_;
v___y_3109_ = v___y_3127_;
v___y_3110_ = v___y_3128_;
v___y_3111_ = v___y_3129_;
v___y_3112_ = v___y_3130_;
v___y_3113_ = v___y_3131_;
v___y_3114_ = v___y_3132_;
v___y_3115_ = v___y_3133_;
v___y_3116_ = v___y_3134_;
v___y_3117_ = v___y_3135_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
goto v___jp_3105_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3251_, lean_object* v_c_x3f_3252_, lean_object* v_cs_x27_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3251_, v_c_x3f_3252_, v_cs_x27_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
lean_dec(v_a_3255_);
lean_dec(v_a_3254_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3266_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3313_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3313_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3313_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
uint8_t v___x_3282_; 
v___x_3282_ = lean_unbox(v_a_3278_);
lean_dec(v_a_3278_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
lean_del_object(v___x_3280_);
v___x_3283_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3300_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3300_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3300_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_unbox(v_a_3284_);
lean_dec(v_a_3284_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v_toGoalState_3290_; lean_object* v_split_3291_; lean_object* v_candidates_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_del_object(v___x_3286_);
v___x_3289_ = lean_st_ref_get(v_a_3266_);
v_toGoalState_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc_ref(v_toGoalState_3290_);
lean_dec(v___x_3289_);
v_split_3291_ = lean_ctor_get(v_toGoalState_3290_, 15);
lean_inc_ref(v_split_3291_);
lean_dec_ref(v_toGoalState_3290_);
v_candidates_3292_ = lean_ctor_get(v_split_3291_, 0);
lean_inc(v_candidates_3292_);
lean_dec_ref(v_split_3291_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_box(0);
v___x_3295_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3292_, v___x_3293_, v___x_3294_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
return v___x_3295_;
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(0);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3296_);
v___x_3298_ = v___x_3286_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
v_a_3301_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3283_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3283_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = lean_box(0);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3309_);
v___x_3311_ = v___x_3280_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
v_a_3314_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3277_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3277_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec(v_a_3322_);
return v_res_3333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_box(0);
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3343_ = l_Lean_mkConst(v___x_3342_, v___x_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3344_){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3346_ = l_Lean_Expr_app___override(v___x_3345_, v_c_3344_);
return v___x_3346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3354_ = l_Lean_mkConst(v___x_3353_, v___x_3352_);
return v___x_3354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = lean_box(0);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4));
v___x_3362_ = l_Lean_mkConst(v___x_3361_, v___x_3360_);
return v___x_3362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = lean_box(0);
v___x_3369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7));
v___x_3370_ = l_Lean_mkConst(v___x_3369_, v___x_3368_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___x_3432_; 
lean_inc_ref(v_c_3371_);
v___x_3432_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3371_, v_a_3379_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3505_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3505_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3505_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = l_Lean_Expr_cleanupAnnotations(v_a_3433_);
lean_dec(v_a_3433_);
v___x_3438_ = l_Lean_Expr_isApp(v___x_3437_);
if (v___x_3438_ == 0)
{
lean_dec_ref(v___x_3437_);
lean_del_object(v___x_3435_);
v___y_3392_ = v_a_3372_;
v___y_3393_ = v_a_3373_;
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v_arg_3439_ = lean_ctor_get(v___x_3437_, 1);
lean_inc_ref(v_arg_3439_);
v___x_3440_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3442_ = l_Lean_Expr_isConstOf(v___x_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
uint8_t v___x_3443_; 
v___x_3443_ = l_Lean_Expr_isApp(v___x_3440_);
if (v___x_3443_ == 0)
{
lean_dec_ref(v___x_3440_);
lean_dec_ref(v_arg_3439_);
lean_del_object(v___x_3435_);
v___y_3392_ = v_a_3372_;
v___y_3393_ = v_a_3373_;
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_arg_3444_ = lean_ctor_get(v___x_3440_, 1);
lean_inc_ref(v_arg_3444_);
v___x_3445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3440_);
lean_dec_ref(v___x_3440_);
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_3447_ = l_Lean_Expr_isConstOf(v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
uint8_t v___x_3448_; 
v___x_3448_ = l_Lean_Expr_isApp(v___x_3445_);
if (v___x_3448_ == 0)
{
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
lean_del_object(v___x_3435_);
v___y_3392_ = v_a_3372_;
v___y_3393_ = v_a_3373_;
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3449_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3445_);
lean_dec_ref(v___x_3445_);
v___x_3450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20));
v___x_3451_ = l_Lean_Expr_isConstOf(v___x_3449_, v___x_3450_);
lean_dec_ref(v___x_3449_);
if (v___x_3451_ == 0)
{
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
lean_del_object(v___x_3435_);
v___y_3392_ = v_a_3372_;
v___y_3393_ = v_a_3373_;
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
goto v___jp_3391_;
}
else
{
uint8_t v___x_3452_; 
v___x_3452_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3371_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
v___x_3453_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3371_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3453_);
v___x_3455_ = v___x_3435_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
else
{
lean_object* v___x_3457_; 
lean_del_object(v___x_3435_);
lean_inc_ref(v_c_3371_);
v___x_3457_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3371_, v_a_3372_, v_a_3376_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; uint8_t v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = lean_unbox(v_a_3458_);
lean_dec(v_a_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3470_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2);
v___x_3466_ = l_Lean_mkApp3(v___x_3465_, v_arg_3444_, v_arg_3439_, v_a_3461_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3466_);
v___x_3468_ = v___x_3463_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
else
{
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
return v___x_3460_;
}
}
else
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3481_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5);
v___x_3477_ = l_Lean_mkApp3(v___x_3476_, v_arg_3444_, v_arg_3439_, v_a_3472_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3477_);
v___x_3479_ = v___x_3474_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
else
{
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
lean_dec_ref(v_c_3371_);
v_a_3482_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3457_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3457_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
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
}
}
}
else
{
lean_object* v___x_3490_; 
lean_dec_ref(v___x_3445_);
lean_del_object(v___x_3435_);
v___x_3490_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3500_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8);
v___x_3496_ = l_Lean_mkApp3(v___x_3495_, v_arg_3444_, v_arg_3439_, v_a_3491_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_dec_ref(v_arg_3444_);
lean_dec_ref(v_arg_3439_);
return v___x_3490_;
}
}
}
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
lean_dec_ref(v___x_3440_);
lean_dec_ref(v_c_3371_);
v___x_3501_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3439_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3501_);
v___x_3503_ = v___x_3435_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3371_);
return v___x_3432_;
}
v___jp_3383_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3384_ = lean_unsigned_to_nat(1u);
v___x_3385_ = l_Lean_Expr_getAppNumArgs(v_c_3371_);
v___x_3386_ = lean_nat_sub(v___x_3385_, v___x_3384_);
lean_dec(v___x_3385_);
v___x_3387_ = lean_nat_sub(v___x_3386_, v___x_3384_);
lean_dec(v___x_3386_);
v___x_3388_ = l_Lean_Expr_getRevArg_x21(v_c_3371_, v___x_3387_);
lean_dec_ref(v_c_3371_);
v___x_3389_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3388_);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
v___jp_3391_:
{
uint8_t v___x_3402_; 
v___x_3402_ = l_Lean_Meta_Grind_isIte(v_c_3371_);
if (v___x_3402_ == 0)
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_Meta_Grind_isDIte(v_c_3371_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_inc_ref(v_c_3371_);
v___x_3404_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3371_, v___y_3392_, v___y_3396_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3423_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3423_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3423_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_unbox(v_a_3405_);
lean_dec(v_a_3405_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3411_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v_c_3371_);
v___x_3411_ = v___x_3407_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_c_3371_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
else
{
lean_object* v___x_3413_; 
lean_del_object(v___x_3407_);
lean_inc_ref(v_c_3371_);
v___x_3413_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3371_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3422_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3371_, v_a_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
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
else
{
lean_dec_ref(v_c_3371_);
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_c_3371_);
v_a_3424_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3404_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3404_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
else
{
goto v___jp_3383_;
}
}
else
{
goto v___jp_3383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec(v_a_3507_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3519_, lean_object* v_major_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3521_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; uint8_t v_trace_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v_trace_3530_ = lean_ctor_get_uint8(v_a_3529_, sizeof(void*)*18);
lean_dec(v_a_3529_);
if (v_trace_3530_ == 0)
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Meta_Grind_cases(v_mvarId_3519_, v_major_3520_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
return v___x_3531_;
}
else
{
lean_object* v___x_3532_; 
lean_inc(v_a_3526_);
lean_inc_ref(v_a_3525_);
lean_inc(v_a_3524_);
lean_inc_ref(v_a_3523_);
lean_inc_ref(v_major_3520_);
v___x_3532_ = lean_infer_type(v_major_3520_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3534_ = l_Lean_Meta_whnfD(v_a_3533_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = l_Lean_Expr_getAppFn(v_a_3535_);
lean_dec(v_a_3535_);
if (lean_obj_tag(v___x_3536_) == 4)
{
lean_object* v_declName_3537_; lean_object* v___x_3538_; 
v_declName_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_declName_3537_);
lean_dec_ref_known(v___x_3536_, 2);
v___x_3538_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3537_, v_a_3522_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3539_; 
lean_dec_ref_known(v___x_3538_, 1);
v___x_3539_ = l_Lean_Meta_Grind_cases(v_mvarId_3519_, v_major_3520_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
return v___x_3539_;
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v_major_3520_);
lean_dec(v_mvarId_3519_);
v_a_3540_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3538_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v___x_3548_; 
lean_dec_ref(v___x_3536_);
v___x_3548_ = l_Lean_Meta_Grind_cases(v_mvarId_3519_, v_major_3520_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
return v___x_3548_;
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v_major_3520_);
lean_dec(v_mvarId_3519_);
v_a_3549_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3534_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3534_);
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
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v_major_3520_);
lean_dec(v_mvarId_3519_);
v_a_3557_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3532_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3532_);
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
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v_major_3520_);
lean_dec(v_mvarId_3519_);
v_a_3565_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3528_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3528_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3573_, lean_object* v_major_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3573_, v_major_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3583_, lean_object* v_major_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3583_, v_major_3584_, v_a_3587_, v_a_3588_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3597_, lean_object* v_major_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3597_, v_major_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec(v_a_3599_);
return v_res_3610_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3611_){
_start:
{
uint64_t v_anchor_3612_; 
v_anchor_3612_ = lean_ctor_get_uint64(v_e_3611_, sizeof(void*)*3);
return v_anchor_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3613_){
_start:
{
uint64_t v_res_3614_; lean_object* v_r_3615_; 
v_res_3614_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3613_);
lean_dec_ref(v_e_3613_);
v_r_3615_ = lean_box_uint64(v_res_3614_);
return v_r_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3618_, lean_object* v_x_3619_){
_start:
{
if (lean_obj_tag(v_x_3619_) == 0)
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_box(0);
return v___x_3620_;
}
else
{
lean_object* v_key_3621_; lean_object* v_value_3622_; lean_object* v_tail_3623_; uint64_t v___x_3624_; uint8_t v___x_3625_; 
v_key_3621_ = lean_ctor_get(v_x_3619_, 0);
v_value_3622_ = lean_ctor_get(v_x_3619_, 1);
v_tail_3623_ = lean_ctor_get(v_x_3619_, 2);
v___x_3624_ = lean_unbox_uint64(v_key_3621_);
v___x_3625_ = lean_uint64_dec_eq(v___x_3624_, v_a_3618_);
if (v___x_3625_ == 0)
{
v_x_3619_ = v_tail_3623_;
goto _start;
}
else
{
lean_object* v___x_3627_; 
lean_inc(v_value_3622_);
v___x_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_value_3622_);
return v___x_3627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3628_, lean_object* v_x_3629_){
_start:
{
uint64_t v_a_boxed_3630_; lean_object* v_res_3631_; 
v_a_boxed_3630_ = lean_unbox_uint64(v_a_3628_);
lean_dec_ref(v_a_3628_);
v_res_3631_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3630_, v_x_3629_);
lean_dec(v_x_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3632_, uint64_t v_a_3633_){
_start:
{
lean_object* v_buckets_3634_; lean_object* v___x_3635_; uint64_t v___x_3636_; uint64_t v___x_3637_; uint64_t v_fold_3638_; uint64_t v___x_3639_; uint64_t v___x_3640_; uint64_t v___x_3641_; size_t v___x_3642_; size_t v___x_3643_; size_t v___x_3644_; size_t v___x_3645_; size_t v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v_buckets_3634_ = lean_ctor_get(v_m_3632_, 1);
v___x_3635_ = lean_array_get_size(v_buckets_3634_);
v___x_3636_ = 32ULL;
v___x_3637_ = lean_uint64_shift_right(v_a_3633_, v___x_3636_);
v_fold_3638_ = lean_uint64_xor(v_a_3633_, v___x_3637_);
v___x_3639_ = 16ULL;
v___x_3640_ = lean_uint64_shift_right(v_fold_3638_, v___x_3639_);
v___x_3641_ = lean_uint64_xor(v_fold_3638_, v___x_3640_);
v___x_3642_ = lean_uint64_to_usize(v___x_3641_);
v___x_3643_ = lean_usize_of_nat(v___x_3635_);
v___x_3644_ = ((size_t)1ULL);
v___x_3645_ = lean_usize_sub(v___x_3643_, v___x_3644_);
v___x_3646_ = lean_usize_land(v___x_3642_, v___x_3645_);
v___x_3647_ = lean_array_uget_borrowed(v_buckets_3634_, v___x_3646_);
v___x_3648_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3633_, v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3649_, lean_object* v_a_3650_){
_start:
{
uint64_t v_a_boxed_3651_; lean_object* v_res_3652_; 
v_a_boxed_3651_ = lean_unbox_uint64(v_a_3650_);
lean_dec_ref(v_a_3650_);
v_res_3652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3649_, v_a_boxed_3651_);
lean_dec_ref(v_m_3649_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3653_, lean_object* v_x_3654_){
_start:
{
if (lean_obj_tag(v_x_3654_) == 0)
{
return v_x_3653_;
}
else
{
lean_object* v_key_3655_; lean_object* v_value_3656_; lean_object* v_tail_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3681_; 
v_key_3655_ = lean_ctor_get(v_x_3654_, 0);
v_value_3656_ = lean_ctor_get(v_x_3654_, 1);
v_tail_3657_ = lean_ctor_get(v_x_3654_, 2);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_x_3654_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3659_ = v_x_3654_;
v_isShared_3660_ = v_isSharedCheck_3681_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_tail_3657_);
lean_inc(v_value_3656_);
lean_inc(v_key_3655_);
lean_dec(v_x_3654_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3681_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; uint64_t v___x_3662_; uint64_t v___x_3663_; uint64_t v___x_3664_; uint64_t v___x_3665_; uint64_t v_fold_3666_; uint64_t v___x_3667_; uint64_t v___x_3668_; uint64_t v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; size_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3661_ = lean_array_get_size(v_x_3653_);
v___x_3662_ = 32ULL;
v___x_3663_ = lean_unbox_uint64(v_key_3655_);
v___x_3664_ = lean_uint64_shift_right(v___x_3663_, v___x_3662_);
v___x_3665_ = lean_unbox_uint64(v_key_3655_);
v_fold_3666_ = lean_uint64_xor(v___x_3665_, v___x_3664_);
v___x_3667_ = 16ULL;
v___x_3668_ = lean_uint64_shift_right(v_fold_3666_, v___x_3667_);
v___x_3669_ = lean_uint64_xor(v_fold_3666_, v___x_3668_);
v___x_3670_ = lean_uint64_to_usize(v___x_3669_);
v___x_3671_ = lean_usize_of_nat(v___x_3661_);
v___x_3672_ = ((size_t)1ULL);
v___x_3673_ = lean_usize_sub(v___x_3671_, v___x_3672_);
v___x_3674_ = lean_usize_land(v___x_3670_, v___x_3673_);
v___x_3675_ = lean_array_uget_borrowed(v_x_3653_, v___x_3674_);
lean_inc(v___x_3675_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 2, v___x_3675_);
v___x_3677_ = v___x_3659_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_key_3655_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_value_3656_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_array_uset(v_x_3653_, v___x_3674_, v___x_3677_);
v_x_3653_ = v___x_3678_;
v_x_3654_ = v_tail_3657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3682_, lean_object* v_source_3683_, lean_object* v_target_3684_){
_start:
{
lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3685_ = lean_array_get_size(v_source_3683_);
v___x_3686_ = lean_nat_dec_lt(v_i_3682_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_dec_ref(v_source_3683_);
lean_dec(v_i_3682_);
return v_target_3684_;
}
else
{
lean_object* v_es_3687_; lean_object* v___x_3688_; lean_object* v_source_3689_; lean_object* v_target_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_es_3687_ = lean_array_fget(v_source_3683_, v_i_3682_);
v___x_3688_ = lean_box(0);
v_source_3689_ = lean_array_fset(v_source_3683_, v_i_3682_, v___x_3688_);
v_target_3690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3684_, v_es_3687_);
v___x_3691_ = lean_unsigned_to_nat(1u);
v___x_3692_ = lean_nat_add(v_i_3682_, v___x_3691_);
lean_dec(v_i_3682_);
v_i_3682_ = v___x_3692_;
v_source_3683_ = v_source_3689_;
v_target_3684_ = v_target_3690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3694_){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v_nbuckets_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3695_ = lean_array_get_size(v_data_3694_);
v___x_3696_ = lean_unsigned_to_nat(2u);
v_nbuckets_3697_ = lean_nat_mul(v___x_3695_, v___x_3696_);
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_mk_array(v_nbuckets_3697_, v___x_3699_);
v___x_3701_ = lean_array_propagate_mark(v_data_3694_, v___x_3700_);
v___x_3702_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3698_, v_data_3694_, v___x_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3703_, lean_object* v_b_3704_, lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 0)
{
lean_dec(v_b_3704_);
return v_x_3705_;
}
else
{
lean_object* v_key_3706_; lean_object* v_value_3707_; lean_object* v_tail_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3722_; 
v_key_3706_ = lean_ctor_get(v_x_3705_, 0);
v_value_3707_ = lean_ctor_get(v_x_3705_, 1);
v_tail_3708_ = lean_ctor_get(v_x_3705_, 2);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_x_3705_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3710_ = v_x_3705_;
v_isShared_3711_ = v_isSharedCheck_3722_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_tail_3708_);
lean_inc(v_value_3707_);
lean_inc(v_key_3706_);
lean_dec(v_x_3705_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3722_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
uint64_t v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = lean_unbox_uint64(v_key_3706_);
v___x_3713_ = lean_uint64_dec_eq(v___x_3712_, v_a_3703_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
v___x_3714_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3703_, v_b_3704_, v_tail_3708_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 2, v___x_3714_);
v___x_3716_ = v___x_3710_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_key_3706_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_value_3707_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec(v_value_3707_);
lean_dec(v_key_3706_);
v___x_3718_ = lean_box_uint64(v_a_3703_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v_b_3704_);
lean_ctor_set(v___x_3710_, 0, v___x_3718_);
v___x_3720_ = v___x_3710_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_b_3704_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_tail_3708_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3723_, lean_object* v_b_3724_, lean_object* v_x_3725_){
_start:
{
uint64_t v_a_boxed_3726_; lean_object* v_res_3727_; 
v_a_boxed_3726_ = lean_unbox_uint64(v_a_3723_);
lean_dec_ref(v_a_3723_);
v_res_3727_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3726_, v_b_3724_, v_x_3725_);
return v_res_3727_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3728_, lean_object* v_x_3729_){
_start:
{
if (lean_obj_tag(v_x_3729_) == 0)
{
uint8_t v___x_3730_; 
v___x_3730_ = 0;
return v___x_3730_;
}
else
{
lean_object* v_key_3731_; lean_object* v_tail_3732_; uint64_t v___x_3733_; uint8_t v___x_3734_; 
v_key_3731_ = lean_ctor_get(v_x_3729_, 0);
v_tail_3732_ = lean_ctor_get(v_x_3729_, 2);
v___x_3733_ = lean_unbox_uint64(v_key_3731_);
v___x_3734_ = lean_uint64_dec_eq(v___x_3733_, v_a_3728_);
if (v___x_3734_ == 0)
{
v_x_3729_ = v_tail_3732_;
goto _start;
}
else
{
return v___x_3734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3736_, lean_object* v_x_3737_){
_start:
{
uint64_t v_a_boxed_3738_; uint8_t v_res_3739_; lean_object* v_r_3740_; 
v_a_boxed_3738_ = lean_unbox_uint64(v_a_3736_);
lean_dec_ref(v_a_3736_);
v_res_3739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3738_, v_x_3737_);
lean_dec(v_x_3737_);
v_r_3740_ = lean_box(v_res_3739_);
return v_r_3740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3741_, uint64_t v_a_3742_, lean_object* v_b_3743_){
_start:
{
lean_object* v_size_3744_; lean_object* v_buckets_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3788_; 
v_size_3744_ = lean_ctor_get(v_m_3741_, 0);
v_buckets_3745_ = lean_ctor_get(v_m_3741_, 1);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_m_3741_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3747_ = v_m_3741_;
v_isShared_3748_ = v_isSharedCheck_3788_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_buckets_3745_);
lean_inc(v_size_3744_);
lean_dec(v_m_3741_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3788_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; uint64_t v___x_3750_; uint64_t v___x_3751_; uint64_t v_fold_3752_; uint64_t v___x_3753_; uint64_t v___x_3754_; uint64_t v___x_3755_; size_t v___x_3756_; size_t v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; size_t v___x_3760_; lean_object* v_bkt_3761_; uint8_t v___x_3762_; 
v___x_3749_ = lean_array_get_size(v_buckets_3745_);
v___x_3750_ = 32ULL;
v___x_3751_ = lean_uint64_shift_right(v_a_3742_, v___x_3750_);
v_fold_3752_ = lean_uint64_xor(v_a_3742_, v___x_3751_);
v___x_3753_ = 16ULL;
v___x_3754_ = lean_uint64_shift_right(v_fold_3752_, v___x_3753_);
v___x_3755_ = lean_uint64_xor(v_fold_3752_, v___x_3754_);
v___x_3756_ = lean_uint64_to_usize(v___x_3755_);
v___x_3757_ = lean_usize_of_nat(v___x_3749_);
v___x_3758_ = ((size_t)1ULL);
v___x_3759_ = lean_usize_sub(v___x_3757_, v___x_3758_);
v___x_3760_ = lean_usize_land(v___x_3756_, v___x_3759_);
v_bkt_3761_ = lean_array_uget_borrowed(v_buckets_3745_, v___x_3760_);
v___x_3762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3742_, v_bkt_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; lean_object* v_size_x27_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v_buckets_x27_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3763_ = lean_unsigned_to_nat(1u);
v_size_x27_3764_ = lean_nat_add(v_size_3744_, v___x_3763_);
lean_dec(v_size_3744_);
v___x_3765_ = lean_box_uint64(v_a_3742_);
lean_inc(v_bkt_3761_);
v___x_3766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v_b_3743_);
lean_ctor_set(v___x_3766_, 2, v_bkt_3761_);
v_buckets_x27_3767_ = lean_array_uset(v_buckets_3745_, v___x_3760_, v___x_3766_);
v___x_3768_ = lean_unsigned_to_nat(4u);
v___x_3769_ = lean_nat_mul(v_size_x27_3764_, v___x_3768_);
v___x_3770_ = lean_unsigned_to_nat(3u);
v___x_3771_ = lean_nat_div(v___x_3769_, v___x_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_array_get_size(v_buckets_x27_3767_);
v___x_3773_ = lean_nat_dec_le(v___x_3771_, v___x_3772_);
lean_dec(v___x_3771_);
if (v___x_3773_ == 0)
{
lean_object* v_val_3774_; lean_object* v___x_3776_; 
v_val_3774_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3767_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 1, v_val_3774_);
lean_ctor_set(v___x_3747_, 0, v_size_x27_3764_);
v___x_3776_ = v___x_3747_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_size_x27_3764_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_val_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
else
{
lean_object* v___x_3779_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 1, v_buckets_x27_3767_);
lean_ctor_set(v___x_3747_, 0, v_size_x27_3764_);
v___x_3779_ = v___x_3747_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_size_x27_3764_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_buckets_x27_3767_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
else
{
lean_object* v___x_3781_; lean_object* v_buckets_x27_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_inc(v_bkt_3761_);
v___x_3781_ = lean_box(0);
v_buckets_x27_3782_ = lean_array_uset(v_buckets_3745_, v___x_3760_, v___x_3781_);
v___x_3783_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3742_, v_b_3743_, v_bkt_3761_);
v___x_3784_ = lean_array_uset(v_buckets_x27_3782_, v___x_3760_, v___x_3783_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 1, v___x_3784_);
v___x_3786_ = v___x_3747_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_size_3744_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3789_, lean_object* v_a_3790_, lean_object* v_b_3791_){
_start:
{
uint64_t v_a_boxed_3792_; lean_object* v_res_3793_; 
v_a_boxed_3792_ = lean_unbox_uint64(v_a_3790_);
lean_dec_ref(v_a_3790_);
v_res_3793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3789_, v_a_boxed_3792_, v_b_3791_);
return v_res_3793_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = lean_box(0);
v___x_3795_ = lean_unsigned_to_nat(16u);
v___x_3796_ = lean_mk_array(v___x_3795_, v___x_3794_);
return v___x_3796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v_found_3799_; 
v___x_3797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3798_ = lean_unsigned_to_nat(0u);
v_found_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3799_, 0, v___x_3798_);
lean_ctor_set(v_found_3799_, 1, v___x_3797_);
return v_found_3799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_found_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3801_ = lean_box(0);
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v_found_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3803_, lean_object* v_numDigits_3804_, lean_object* v_es_3805_, lean_object* v_as_3806_, size_t v_sz_3807_, size_t v_i_3808_, lean_object* v_b_3809_){
_start:
{
lean_object* v_a_3811_; uint8_t v___x_3815_; 
v___x_3815_ = lean_usize_dec_lt(v_i_3808_, v_sz_3807_);
if (v___x_3815_ == 0)
{
return v_b_3809_;
}
else
{
lean_object* v_snd_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3850_; 
v_snd_3816_ = lean_ctor_get(v_b_3809_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_b_3809_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_b_3809_, 0);
lean_dec(v_unused_3851_);
v___x_3818_ = v_b_3809_;
v_isShared_3819_ = v_isSharedCheck_3850_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_snd_3816_);
lean_dec(v_b_3809_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3850_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_a_3820_; uint64_t v_anchor_3821_; lean_object* v___x_3822_; uint64_t v___x_3823_; uint64_t v___x_3824_; lean_object* v___x_3825_; 
v_a_3820_ = lean_array_uget_borrowed(v_as_3806_, v_i_3808_);
v_anchor_3821_ = lean_ctor_get_uint64(v_a_3820_, sizeof(void*)*3);
v___x_3822_ = lean_box(0);
v___x_3823_ = lean_uint64_of_nat(v_shift_3803_);
v___x_3824_ = lean_uint64_shift_right(v_anchor_3821_, v___x_3823_);
v___x_3825_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3816_, v___x_3824_);
if (lean_obj_tag(v___x_3825_) == 1)
{
lean_object* v_val_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3844_; 
v_val_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3844_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_val_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3844_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
uint64_t v___x_3830_; uint8_t v___x_3831_; 
v___x_3830_ = lean_unbox_uint64(v_val_3826_);
lean_dec(v_val_3826_);
v___x_3831_ = lean_uint64_dec_eq(v___x_3830_, v_anchor_3821_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3832_ = lean_unsigned_to_nat(1u);
v___x_3833_ = lean_nat_add(v_numDigits_3804_, v___x_3832_);
v___x_3834_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3805_, v___x_3833_);
lean_dec(v___x_3833_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3834_);
v___x_3836_ = v___x_3828_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3838_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3836_);
v___x_3838_ = v___x_3818_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_snd_3816_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
else
{
lean_object* v___x_3842_; 
lean_del_object(v___x_3828_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3822_);
v___x_3842_ = v___x_3818_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_snd_3816_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
v_a_3811_ = v___x_3842_;
goto v___jp_3810_;
}
}
}
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
lean_dec(v___x_3825_);
v___x_3845_ = lean_box_uint64(v_anchor_3821_);
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3816_, v___x_3824_, v___x_3845_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 1, v___x_3846_);
lean_ctor_set(v___x_3818_, 0, v___x_3822_);
v___x_3848_ = v___x_3818_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
v_a_3811_ = v___x_3848_;
goto v___jp_3810_;
}
}
}
}
v___jp_3810_:
{
size_t v___x_3812_; size_t v___x_3813_; 
v___x_3812_ = ((size_t)1ULL);
v___x_3813_ = lean_usize_add(v_i_3808_, v___x_3812_);
v_i_3808_ = v___x_3813_;
v_b_3809_ = v_a_3811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3852_, lean_object* v_numDigits_3853_){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v___x_3854_ = lean_unsigned_to_nat(4u);
v___x_3855_ = lean_nat_mul(v___x_3854_, v_numDigits_3853_);
v___x_3856_ = lean_unsigned_to_nat(64u);
v___x_3857_ = lean_nat_dec_lt(v___x_3855_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_dec(v___x_3855_);
lean_inc(v_numDigits_3853_);
return v_numDigits_3853_;
}
else
{
lean_object* v_shift_3858_; lean_object* v___x_3859_; size_t v_sz_3860_; size_t v___x_3861_; lean_object* v___x_3862_; lean_object* v_fst_3863_; 
v_shift_3858_ = lean_nat_sub(v___x_3856_, v___x_3855_);
lean_dec(v___x_3855_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3860_ = lean_array_size(v_es_3852_);
v___x_3861_ = ((size_t)0ULL);
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3858_, v_numDigits_3853_, v_es_3852_, v_es_3852_, v_sz_3860_, v___x_3861_, v___x_3859_);
lean_dec(v_shift_3858_);
v_fst_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_fst_3863_);
lean_dec_ref(v___x_3862_);
if (lean_obj_tag(v_fst_3863_) == 0)
{
lean_inc(v_numDigits_3853_);
return v_numDigits_3853_;
}
else
{
lean_object* v_val_3864_; 
v_val_3864_ = lean_ctor_get(v_fst_3863_, 0);
lean_inc(v_val_3864_);
lean_dec_ref_known(v_fst_3863_, 1);
return v_val_3864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3865_, lean_object* v_numDigits_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3865_, v_numDigits_3866_);
lean_dec(v_numDigits_3866_);
lean_dec_ref(v_es_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3868_, lean_object* v_numDigits_3869_, lean_object* v_es_3870_, lean_object* v_as_3871_, lean_object* v_sz_3872_, lean_object* v_i_3873_, lean_object* v_b_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3872_);
lean_dec(v_sz_3872_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3873_);
lean_dec(v_i_3873_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3868_, v_numDigits_3869_, v_es_3870_, v_as_3871_, v_sz_boxed_3875_, v_i_boxed_3876_, v_b_3874_);
lean_dec_ref(v_as_3871_);
lean_dec_ref(v_es_3870_);
lean_dec(v_numDigits_3869_);
lean_dec(v_shift_3868_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3878_){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_unsigned_to_nat(4u);
v___x_3880_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3878_, v___x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3881_);
lean_dec_ref(v_es_3881_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3883_, lean_object* v_as_3884_, size_t v_i_3885_, size_t v_stop_3886_, lean_object* v_b_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_a_3900_; uint8_t v___x_3904_; 
v___x_3904_ = lean_usize_dec_eq(v_i_3885_, v_stop_3886_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v_e_3906_; lean_object* v___x_3907_; 
v___x_3905_ = lean_array_uget_borrowed(v_as_3884_, v_i_3885_);
v_e_3906_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3905_);
v___x_3907_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3905_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
lean_inc(v___x_3905_);
v___x_3909_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3905_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
if (lean_obj_tag(v_a_3910_) == 2)
{
lean_object* v_numCases_3911_; uint8_t v_isRec_3912_; lean_object* v___x_3913_; 
v_numCases_3911_ = lean_ctor_get(v_a_3910_, 0);
lean_inc(v_numCases_3911_);
v_isRec_3912_ = lean_ctor_get_uint8(v_a_3910_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3910_, 1);
lean_inc_ref(v_filter_3883_);
lean_inc(v___y_3897_);
lean_inc_ref(v___y_3896_);
lean_inc(v___y_3895_);
lean_inc_ref(v___y_3894_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc(v___y_3888_);
lean_inc_ref(v_e_3906_);
v___x_3913_ = lean_apply_12(v_filter_3883_, v_e_3906_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, lean_box(0));
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; uint8_t v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = lean_unbox(v_a_3914_);
lean_dec(v_a_3914_);
if (v___x_3915_ == 0)
{
lean_dec(v_numCases_3911_);
lean_dec(v_a_3908_);
lean_dec_ref(v_e_3906_);
v_a_3900_ = v_b_3887_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3916_; uint64_t v___x_3917_; lean_object* v___x_3918_; 
lean_inc(v___x_3905_);
v___x_3916_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3916_, 0, v___x_3905_);
lean_ctor_set(v___x_3916_, 1, v_numCases_3911_);
lean_ctor_set(v___x_3916_, 2, v_e_3906_);
lean_ctor_set_uint8(v___x_3916_, sizeof(void*)*3 + 8, v_isRec_3912_);
v___x_3917_ = lean_unbox_uint64(v_a_3908_);
lean_dec(v_a_3908_);
lean_ctor_set_uint64(v___x_3916_, sizeof(void*)*3, v___x_3917_);
v___x_3918_ = lean_array_push(v_b_3887_, v___x_3916_);
v_a_3900_ = v___x_3918_;
goto v___jp_3899_;
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v_numCases_3911_);
lean_dec(v_a_3908_);
lean_dec_ref(v_e_3906_);
lean_dec_ref(v_b_3887_);
lean_dec_ref(v_filter_3883_);
v_a_3919_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3913_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3913_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_dec(v_a_3910_);
lean_dec(v_a_3908_);
lean_dec_ref(v_e_3906_);
v_a_3900_ = v_b_3887_;
goto v___jp_3899_;
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v_a_3908_);
lean_dec_ref(v_e_3906_);
lean_dec_ref(v_b_3887_);
lean_dec_ref(v_filter_3883_);
v_a_3927_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3909_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3909_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v_e_3906_);
lean_dec_ref(v_b_3887_);
lean_dec_ref(v_filter_3883_);
v_a_3935_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3907_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3907_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v___x_3943_; 
lean_dec_ref(v_filter_3883_);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v_b_3887_);
return v___x_3943_;
}
v___jp_3899_:
{
size_t v___x_3901_; size_t v___x_3902_; 
v___x_3901_ = ((size_t)1ULL);
v___x_3902_ = lean_usize_add(v_i_3885_, v___x_3901_);
v_i_3885_ = v___x_3902_;
v_b_3887_ = v_a_3900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3944_, lean_object* v_as_3945_, lean_object* v_i_3946_, lean_object* v_stop_3947_, lean_object* v_b_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
size_t v_i_boxed_3960_; size_t v_stop_boxed_3961_; lean_object* v_res_3962_; 
v_i_boxed_3960_ = lean_unbox_usize(v_i_3946_);
lean_dec(v_i_3946_);
v_stop_boxed_3961_ = lean_unbox_usize(v_stop_3947_);
lean_dec(v_stop_3947_);
v_res_3962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3944_, v_as_3945_, v_i_boxed_3960_, v_stop_boxed_3961_, v_b_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v_as_3945_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3965_, lean_object* v_as_3966_, lean_object* v_start_3967_, lean_object* v_stop_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3981_ = lean_nat_dec_lt(v_start_3967_, v_stop_3968_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; 
lean_dec_ref(v_filter_3965_);
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
return v___x_3982_;
}
else
{
lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3983_ = lean_array_get_size(v_as_3966_);
v___x_3984_ = lean_nat_dec_le(v_stop_3968_, v___x_3983_);
if (v___x_3984_ == 0)
{
uint8_t v___x_3985_; 
v___x_3985_ = lean_nat_dec_lt(v_start_3967_, v___x_3983_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref(v_filter_3965_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3980_);
return v___x_3986_;
}
else
{
size_t v___x_3987_; size_t v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = lean_usize_of_nat(v_start_3967_);
v___x_3988_ = lean_usize_of_nat(v___x_3983_);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3965_, v_as_3966_, v___x_3987_, v___x_3988_, v___x_3980_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3989_;
}
}
else
{
size_t v___x_3990_; size_t v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = lean_usize_of_nat(v_start_3967_);
v___x_3991_ = lean_usize_of_nat(v_stop_3968_);
v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3965_, v_as_3966_, v___x_3990_, v___x_3991_, v___x_3980_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3993_, lean_object* v_as_3994_, lean_object* v_start_3995_, lean_object* v_stop_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3993_, v_as_3994_, v_start_3995_, v_stop_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec(v_stop_3996_);
lean_dec(v_start_3995_);
lean_dec_ref(v_as_3994_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_4009_, lean_object* v_candidates_x3f_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_candidates_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; 
if (lean_obj_tag(v_candidates_x3f_4010_) == 0)
{
lean_object* v___x_4056_; lean_object* v_toGoalState_4057_; lean_object* v_split_4058_; lean_object* v_candidates_4059_; 
v___x_4056_ = lean_st_ref_get(v_a_4011_);
v_toGoalState_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc_ref(v_toGoalState_4057_);
lean_dec(v___x_4056_);
v_split_4058_ = lean_ctor_get(v_toGoalState_4057_, 15);
lean_inc_ref(v_split_4058_);
lean_dec_ref(v_toGoalState_4057_);
v_candidates_4059_ = lean_ctor_get(v_split_4058_, 0);
lean_inc(v_candidates_4059_);
lean_dec_ref(v_split_4058_);
v_candidates_4023_ = v_candidates_4059_;
v___y_4024_ = v_a_4011_;
v___y_4025_ = v_a_4012_;
v___y_4026_ = v_a_4013_;
v___y_4027_ = v_a_4014_;
v___y_4028_ = v_a_4015_;
v___y_4029_ = v_a_4016_;
v___y_4030_ = v_a_4017_;
v___y_4031_ = v_a_4018_;
v___y_4032_ = v_a_4019_;
v___y_4033_ = v_a_4020_;
goto v___jp_4022_;
}
else
{
lean_object* v_val_4060_; 
v_val_4060_ = lean_ctor_get(v_candidates_x3f_4010_, 0);
lean_inc(v_val_4060_);
lean_dec_ref_known(v_candidates_x3f_4010_, 1);
v_candidates_4023_ = v_val_4060_;
v___y_4024_ = v_a_4011_;
v___y_4025_ = v_a_4012_;
v___y_4026_ = v_a_4013_;
v___y_4027_ = v_a_4014_;
v___y_4028_ = v_a_4015_;
v___y_4029_ = v_a_4016_;
v___y_4030_ = v_a_4017_;
v___y_4031_ = v_a_4018_;
v___y_4032_ = v_a_4019_;
v___y_4033_ = v_a_4020_;
goto v___jp_4022_;
}
v___jp_4022_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4034_ = lean_array_mk(v_candidates_4023_);
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_array_get_size(v___x_4034_);
v___x_4037_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_4009_, v___x_4034_, v___x_4035_, v___x_4036_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec_ref(v___x_4034_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4047_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4047_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4047_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4045_; 
v___x_4042_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4038_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v_a_4038_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4043_);
v___x_4045_ = v___x_4040_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
v_a_4048_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4037_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4037_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4061_, lean_object* v_candidates_x3f_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4061_, v_candidates_x3f_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec(v_a_4063_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4075_, lean_object* v_m_4076_, uint64_t v_a_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4076_, v_a_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4079_, lean_object* v_m_4080_, lean_object* v_a_4081_){
_start:
{
uint64_t v_a_boxed_4082_; lean_object* v_res_4083_; 
v_a_boxed_4082_ = lean_unbox_uint64(v_a_4081_);
lean_dec_ref(v_a_4081_);
v_res_4083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4079_, v_m_4080_, v_a_boxed_4082_);
lean_dec_ref(v_m_4080_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4084_, lean_object* v_m_4085_, uint64_t v_a_4086_, lean_object* v_b_4087_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4085_, v_a_4086_, v_b_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4089_, lean_object* v_m_4090_, lean_object* v_a_4091_, lean_object* v_b_4092_){
_start:
{
uint64_t v_a_boxed_4093_; lean_object* v_res_4094_; 
v_a_boxed_4093_ = lean_unbox_uint64(v_a_4091_);
lean_dec_ref(v_a_4091_);
v_res_4094_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4089_, v_m_4090_, v_a_boxed_4093_, v_b_4092_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4095_, uint64_t v_a_4096_, lean_object* v_x_4097_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4096_, v_x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4099_, lean_object* v_a_4100_, lean_object* v_x_4101_){
_start:
{
uint64_t v_a_boxed_4102_; lean_object* v_res_4103_; 
v_a_boxed_4102_ = lean_unbox_uint64(v_a_4100_);
lean_dec_ref(v_a_4100_);
v_res_4103_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4099_, v_a_boxed_4102_, v_x_4101_);
lean_dec(v_x_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4104_, uint64_t v_a_4105_, lean_object* v_x_4106_){
_start:
{
uint8_t v___x_4107_; 
v___x_4107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4105_, v_x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4108_, lean_object* v_a_4109_, lean_object* v_x_4110_){
_start:
{
uint64_t v_a_boxed_4111_; uint8_t v_res_4112_; lean_object* v_r_4113_; 
v_a_boxed_4111_ = lean_unbox_uint64(v_a_4109_);
lean_dec_ref(v_a_4109_);
v_res_4112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4108_, v_a_boxed_4111_, v_x_4110_);
lean_dec(v_x_4110_);
v_r_4113_ = lean_box(v_res_4112_);
return v_r_4113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4114_, lean_object* v_data_4115_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4117_, uint64_t v_a_4118_, lean_object* v_b_4119_, lean_object* v_x_4120_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4118_, v_b_4119_, v_x_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4122_, lean_object* v_a_4123_, lean_object* v_b_4124_, lean_object* v_x_4125_){
_start:
{
uint64_t v_a_boxed_4126_; lean_object* v_res_4127_; 
v_a_boxed_4126_ = lean_unbox_uint64(v_a_4123_);
lean_dec_ref(v_a_4123_);
v_res_4127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4122_, v_a_boxed_4126_, v_b_4124_, v_x_4125_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4128_, lean_object* v_i_4129_, lean_object* v_source_4130_, lean_object* v_target_4131_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4129_, v_source_4130_, v_target_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4133_, lean_object* v_x_4134_, lean_object* v_x_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4134_, v_x_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
uint8_t v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = 1;
v___x_4150_ = lean_box(v___x_4149_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v_x_4152_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4165_, uint64_t v_a_4166_, lean_object* v_c_4167_, lean_object* v_numDigits_4168_, lean_object* v_as_4169_, size_t v_sz_4170_, size_t v_i_4171_, lean_object* v_b_4172_){
_start:
{
lean_object* v_a_4175_; uint8_t v___x_4179_; 
v___x_4179_ = lean_usize_dec_lt(v_i_4171_, v_sz_4170_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; 
lean_dec(v_numDigits_4168_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v_b_4172_);
return v___x_4180_;
}
else
{
lean_object* v_snd_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4207_; 
v_snd_4181_ = lean_ctor_get(v_b_4172_, 1);
v_isSharedCheck_4207_ = !lean_is_exclusive(v_b_4172_);
if (v_isSharedCheck_4207_ == 0)
{
lean_object* v_unused_4208_; 
v_unused_4208_ = lean_ctor_get(v_b_4172_, 0);
lean_dec(v_unused_4208_);
v___x_4183_ = v_b_4172_;
v_isShared_4184_ = v_isSharedCheck_4207_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_snd_4181_);
lean_dec(v_b_4172_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4207_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v_a_4185_; lean_object* v_c_4186_; uint64_t v_anchor_4187_; lean_object* v___x_4188_; uint64_t v___x_4189_; uint64_t v___x_4190_; uint8_t v___x_4191_; 
v_a_4185_ = lean_array_uget_borrowed(v_as_4169_, v_i_4171_);
v_c_4186_ = lean_ctor_get(v_a_4185_, 0);
v_anchor_4187_ = lean_ctor_get_uint64(v_a_4185_, sizeof(void*)*3);
v___x_4188_ = lean_box(0);
v___x_4189_ = lean_uint64_shift_right(v_anchor_4187_, v___x_4165_);
v___x_4190_ = lean_uint64_shift_right(v_a_4166_, v___x_4165_);
v___x_4191_ = lean_uint64_dec_eq(v___x_4189_, v___x_4190_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4193_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___x_4188_);
v___x_4193_ = v___x_4183_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_snd_4181_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
v_a_4175_ = v___x_4193_;
goto v___jp_4174_;
}
}
else
{
uint8_t v___x_4195_; 
v___x_4195_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4186_, v_c_4167_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4196_ = lean_unsigned_to_nat(1u);
v___x_4197_ = lean_nat_add(v_snd_4181_, v___x_4196_);
lean_dec(v_snd_4181_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 1, v___x_4197_);
lean_ctor_set(v___x_4183_, 0, v___x_4188_);
v___x_4199_ = v___x_4183_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
v_a_4175_ = v___x_4199_;
goto v___jp_4174_;
}
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
lean_inc(v_snd_4181_);
v___x_4201_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4201_, 0, v_numDigits_4168_);
lean_ctor_set(v___x_4201_, 1, v_snd_4181_);
lean_ctor_set_uint64(v___x_4201_, sizeof(void*)*2, v_a_4166_);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___x_4202_);
v___x_4204_ = v___x_4183_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4202_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v_snd_4181_);
v___x_4204_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
return v___x_4205_;
}
}
}
}
}
v___jp_4174_:
{
size_t v___x_4176_; size_t v___x_4177_; 
v___x_4176_ = ((size_t)1ULL);
v___x_4177_ = lean_usize_add(v_i_4171_, v___x_4176_);
v_i_4171_ = v___x_4177_;
v_b_4172_ = v_a_4175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4209_, lean_object* v_a_4210_, lean_object* v_c_4211_, lean_object* v_numDigits_4212_, lean_object* v_as_4213_, lean_object* v_sz_4214_, lean_object* v_i_4215_, lean_object* v_b_4216_, lean_object* v___y_4217_){
_start:
{
uint64_t v___x_7695__boxed_4218_; uint64_t v_a_7696__boxed_4219_; size_t v_sz_boxed_4220_; size_t v_i_boxed_4221_; lean_object* v_res_4222_; 
v___x_7695__boxed_4218_ = lean_unbox_uint64(v___x_4209_);
lean_dec_ref(v___x_4209_);
v_a_7696__boxed_4219_ = lean_unbox_uint64(v_a_4210_);
lean_dec_ref(v_a_4210_);
v_sz_boxed_4220_ = lean_unbox_usize(v_sz_4214_);
lean_dec(v_sz_4214_);
v_i_boxed_4221_ = lean_unbox_usize(v_i_4215_);
lean_dec(v_i_4215_);
v_res_4222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7695__boxed_4218_, v_a_7696__boxed_4219_, v_c_4211_, v_numDigits_4212_, v_as_4213_, v_sz_boxed_4220_, v_i_boxed_4221_, v_b_4216_);
lean_dec_ref(v_as_4213_);
lean_dec_ref(v_c_4211_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4227_, lean_object* v_candidates_x3f_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___f_4240_; lean_object* v___x_4241_; 
v___f_4240_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4241_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4240_, v_candidates_x3f_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v_candidates_4243_; lean_object* v_numDigits_4244_; lean_object* v___x_4245_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v_candidates_4243_ = lean_ctor_get(v_a_4242_, 0);
lean_inc_ref(v_candidates_4243_);
v_numDigits_4244_ = lean_ctor_get(v_a_4242_, 1);
lean_inc(v_numDigits_4244_);
lean_dec(v_a_4242_);
v___x_4245_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4227_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; uint64_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; size_t v_sz_4254_; size_t v___x_4255_; uint64_t v___x_4256_; lean_object* v___x_4257_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
v___x_4247_ = lean_unsigned_to_nat(64u);
v___x_4248_ = lean_unsigned_to_nat(4u);
v___x_4249_ = lean_nat_mul(v___x_4248_, v_numDigits_4244_);
v___x_4250_ = lean_nat_sub(v___x_4247_, v___x_4249_);
lean_dec(v___x_4249_);
v___x_4251_ = lean_uint64_of_nat(v___x_4250_);
lean_dec(v___x_4250_);
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4254_ = lean_array_size(v_candidates_4243_);
v___x_4255_ = ((size_t)0ULL);
v___x_4256_ = lean_unbox_uint64(v_a_4246_);
lean_inc(v_numDigits_4244_);
v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4251_, v___x_4256_, v_c_4227_, v_numDigits_4244_, v_candidates_4243_, v_sz_4254_, v___x_4255_, v___x_4253_);
lean_dec_ref(v_candidates_4243_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4272_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4272_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4272_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v_fst_4262_; 
v_fst_4262_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_fst_4262_);
lean_dec(v_a_4258_);
if (lean_obj_tag(v_fst_4262_) == 0)
{
lean_object* v___x_4263_; uint64_t v___x_4264_; lean_object* v___x_4266_; 
v___x_4263_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4263_, 0, v_numDigits_4244_);
lean_ctor_set(v___x_4263_, 1, v___x_4252_);
v___x_4264_ = lean_unbox_uint64(v_a_4246_);
lean_dec(v_a_4246_);
lean_ctor_set_uint64(v___x_4263_, sizeof(void*)*2, v___x_4264_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4263_);
v___x_4266_ = v___x_4260_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4263_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
else
{
lean_object* v_val_4268_; lean_object* v___x_4270_; 
lean_dec(v_a_4246_);
lean_dec(v_numDigits_4244_);
v_val_4268_ = lean_ctor_get(v_fst_4262_, 0);
lean_inc(v_val_4268_);
lean_dec_ref_known(v_fst_4262_, 1);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v_val_4268_);
v___x_4270_ = v___x_4260_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_val_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v_a_4246_);
lean_dec(v_numDigits_4244_);
v_a_4273_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4257_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4257_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_numDigits_4244_);
lean_dec_ref(v_candidates_4243_);
v_a_4281_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4245_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4245_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
v_a_4289_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4241_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4241_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4297_, lean_object* v_candidates_x3f_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4297_, v_candidates_x3f_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_c_4297_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4311_, uint64_t v_a_4312_, lean_object* v_c_4313_, lean_object* v_numDigits_4314_, lean_object* v_as_4315_, size_t v_sz_4316_, size_t v_i_4317_, lean_object* v_b_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4311_, v_a_4312_, v_c_4313_, v_numDigits_4314_, v_as_4315_, v_sz_4316_, v_i_4317_, v_b_4318_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4331_ = _args[0];
lean_object* v_a_4332_ = _args[1];
lean_object* v_c_4333_ = _args[2];
lean_object* v_numDigits_4334_ = _args[3];
lean_object* v_as_4335_ = _args[4];
lean_object* v_sz_4336_ = _args[5];
lean_object* v_i_4337_ = _args[6];
lean_object* v_b_4338_ = _args[7];
lean_object* v___y_4339_ = _args[8];
lean_object* v___y_4340_ = _args[9];
lean_object* v___y_4341_ = _args[10];
lean_object* v___y_4342_ = _args[11];
lean_object* v___y_4343_ = _args[12];
lean_object* v___y_4344_ = _args[13];
lean_object* v___y_4345_ = _args[14];
lean_object* v___y_4346_ = _args[15];
lean_object* v___y_4347_ = _args[16];
lean_object* v___y_4348_ = _args[17];
lean_object* v___y_4349_ = _args[18];
_start:
{
uint64_t v___x_7894__boxed_4350_; uint64_t v_a_7895__boxed_4351_; size_t v_sz_boxed_4352_; size_t v_i_boxed_4353_; lean_object* v_res_4354_; 
v___x_7894__boxed_4350_ = lean_unbox_uint64(v___x_4331_);
lean_dec_ref(v___x_4331_);
v_a_7895__boxed_4351_ = lean_unbox_uint64(v_a_4332_);
lean_dec_ref(v_a_4332_);
v_sz_boxed_4352_ = lean_unbox_usize(v_sz_4336_);
lean_dec(v_sz_4336_);
v_i_boxed_4353_ = lean_unbox_usize(v_i_4337_);
lean_dec(v_i_4337_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7894__boxed_4350_, v_a_7895__boxed_4351_, v_c_4333_, v_numDigits_4334_, v_as_4335_, v_sz_boxed_4352_, v_i_boxed_4353_, v_b_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v_as_4335_);
lean_dec_ref(v_c_4333_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_numDigits_4382_; uint64_t v_anchor_4383_; lean_object* v_ordinal_4384_; lean_object* v___x_4385_; 
v_numDigits_4382_ = lean_ctor_get(v_info_4379_, 0);
v_anchor_4383_ = lean_ctor_get_uint64(v_info_4379_, sizeof(void*)*2);
v_ordinal_4384_ = lean_ctor_get(v_info_4379_, 1);
v___x_4385_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4382_, v_anchor_4383_, v_a_4380_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4422_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4422_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4422_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = lean_unsigned_to_nat(0u);
v___x_4391_ = lean_nat_dec_eq(v_ordinal_4384_, v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v_ref_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4408_; 
v_ref_4392_ = lean_ctor_get(v_a_4380_, 2);
v___x_4393_ = l_Lean_SourceInfo_fromRef(v_ref_4392_, v___x_4391_);
v___x_4394_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4395_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4393_, 3);
v___x_4396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4393_);
lean_ctor_set(v___x_4396_, 1, v___x_4394_);
v___x_4397_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4398_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4393_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = lean_unsigned_to_nat(1u);
v___x_4401_ = lean_nat_add(v_ordinal_4384_, v___x_4400_);
v___x_4402_ = l_Nat_reprFast(v___x_4401_);
v___x_4403_ = lean_box(2);
v___x_4404_ = l_Lean_Syntax_mkNumLit(v___x_4402_, v___x_4403_);
v___x_4405_ = l_Lean_Syntax_node3(v___x_4393_, v___x_4397_, v_a_4386_, v___x_4399_, v___x_4404_);
v___x_4406_ = l_Lean_Syntax_node2(v___x_4393_, v___x_4395_, v___x_4396_, v___x_4405_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4406_);
v___x_4408_ = v___x_4388_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
else
{
lean_object* v_ref_4410_; uint8_t v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
v_ref_4410_ = lean_ctor_get(v_a_4380_, 2);
v___x_4411_ = 0;
v___x_4412_ = l_Lean_SourceInfo_fromRef(v_ref_4410_, v___x_4411_);
v___x_4413_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4414_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4412_, 2);
v___x_4415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4412_);
lean_ctor_set(v___x_4415_, 1, v___x_4413_);
v___x_4416_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4417_ = l_Lean_Syntax_node1(v___x_4412_, v___x_4416_, v_a_4386_);
v___x_4418_ = l_Lean_Syntax_node2(v___x_4412_, v___x_4414_, v___x_4415_, v___x_4417_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4418_);
v___x_4420_ = v___x_4388_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
else
{
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4423_, v_a_4424_);
lean_dec_ref(v_a_4424_);
lean_dec_ref(v_info_4423_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4427_, v_a_4428_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4432_, v_a_4433_, v_a_4434_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
lean_dec_ref(v_info_4432_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(lean_object* v_proof_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v_p_4468_; lean_object* v___x_4471_; 
lean_inc_ref(v_proof_4449_);
v___x_4471_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4449_, v_a_4451_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4498_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4474_ = v___x_4471_;
v_isShared_4475_ = v_isSharedCheck_4498_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4471_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4498_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4476_ = l_Lean_Expr_cleanupAnnotations(v_a_4472_);
lean_dec(v_a_4472_);
v___x_4477_ = l_Lean_Expr_isApp(v___x_4476_);
if (v___x_4477_ == 0)
{
lean_dec_ref(v___x_4476_);
lean_del_object(v___x_4474_);
v___y_4456_ = v_a_4450_;
v___y_4457_ = v_a_4451_;
v___y_4458_ = v_a_4452_;
v___y_4459_ = v_a_4453_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4476_);
v___x_4479_ = l_Lean_Expr_isApp(v___x_4478_);
if (v___x_4479_ == 0)
{
lean_dec_ref(v___x_4478_);
lean_dec_ref(v___x_4476_);
lean_del_object(v___x_4474_);
v___y_4456_ = v_a_4450_;
v___y_4457_ = v_a_4451_;
v___y_4458_ = v_a_4452_;
v___y_4459_ = v_a_4453_;
goto v___jp_4455_;
}
else
{
lean_object* v_arg_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; uint8_t v___x_4483_; 
v_arg_4480_ = lean_ctor_get(v___x_4476_, 1);
lean_inc_ref(v_arg_4480_);
lean_dec_ref(v___x_4476_);
v___x_4481_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4478_);
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4483_ = l_Lean_Expr_isConstOf(v___x_4481_, v___x_4482_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; uint8_t v___x_4485_; 
lean_dec_ref(v___x_4478_);
lean_del_object(v___x_4474_);
v___x_4484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4485_ = l_Lean_Expr_isConstOf(v___x_4481_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; uint8_t v___x_4487_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4487_ = l_Lean_Expr_isConstOf(v___x_4481_, v___x_4486_);
lean_dec_ref(v___x_4481_);
if (v___x_4487_ == 0)
{
lean_dec_ref(v_arg_4480_);
v___y_4456_ = v_a_4450_;
v___y_4457_ = v_a_4451_;
v___y_4458_ = v_a_4452_;
v___y_4459_ = v_a_4453_;
goto v___jp_4455_;
}
else
{
lean_dec_ref(v_proof_4449_);
v_p_4468_ = v_arg_4480_;
goto v___jp_4467_;
}
}
else
{
lean_dec_ref(v___x_4481_);
lean_dec_ref(v_proof_4449_);
v_p_4468_ = v_arg_4480_;
goto v___jp_4467_;
}
}
else
{
lean_object* v_arg_4488_; uint8_t v___x_4489_; 
lean_dec_ref(v___x_4481_);
lean_dec_ref(v_proof_4449_);
v_arg_4488_ = lean_ctor_get(v___x_4478_, 1);
lean_inc_ref(v_arg_4488_);
lean_dec_ref(v___x_4478_);
v___x_4489_ = l_Lean_Expr_isFalse(v_arg_4488_);
lean_dec_ref(v_arg_4488_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; lean_object* v___x_4492_; 
lean_dec_ref(v_arg_4480_);
v___x_4490_ = lean_box(0);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4490_);
v___x_4492_ = v___x_4474_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4496_; 
v___x_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4494_, 0, v_arg_4480_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4494_);
v___x_4496_ = v___x_4474_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref(v_proof_4449_);
v_a_4499_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4471_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4471_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
v___jp_4455_:
{
if (lean_obj_tag(v_proof_4449_) == 6)
{
lean_object* v_body_4460_; uint8_t v___x_4461_; 
v_body_4460_ = lean_ctor_get(v_proof_4449_, 2);
lean_inc_ref(v_body_4460_);
lean_dec_ref_known(v_proof_4449_, 3);
v___x_4461_ = l_Lean_Expr_hasLooseBVars(v_body_4460_);
if (v___x_4461_ == 0)
{
v_proof_4449_ = v_body_4460_;
v_a_4450_ = v___y_4456_;
v_a_4451_ = v___y_4457_;
v_a_4452_ = v___y_4458_;
v_a_4453_ = v___y_4459_;
goto _start;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
lean_dec_ref(v_body_4460_);
v___x_4463_ = lean_box(0);
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
}
else
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_dec_ref(v_proof_4449_);
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
return v___x_4466_;
}
}
v___jp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4469_, 0, v_p_4468_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___boxed(lean_object* v_proof_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_proof_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(lean_object* v_e_4514_, lean_object* v___y_4515_){
_start:
{
uint8_t v___x_4517_; 
v___x_4517_ = l_Lean_Expr_hasMVar(v_e_4514_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_e_4514_);
return v___x_4518_;
}
else
{
lean_object* v___x_4519_; lean_object* v_mctx_4520_; lean_object* v___x_4521_; lean_object* v_fst_4522_; lean_object* v_snd_4523_; lean_object* v___x_4524_; lean_object* v_cache_4525_; lean_object* v_zetaDeltaFVarIds_4526_; lean_object* v_postponed_4527_; lean_object* v_diag_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4537_; 
v___x_4519_ = lean_st_ref_get(v___y_4515_);
v_mctx_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc_ref(v_mctx_4520_);
lean_dec(v___x_4519_);
v___x_4521_ = l_Lean_instantiateMVarsCore(v_mctx_4520_, v_e_4514_);
v_fst_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_fst_4522_);
v_snd_4523_ = lean_ctor_get(v___x_4521_, 1);
lean_inc(v_snd_4523_);
lean_dec_ref(v___x_4521_);
v___x_4524_ = lean_st_ref_take(v___y_4515_);
v_cache_4525_ = lean_ctor_get(v___x_4524_, 1);
v_zetaDeltaFVarIds_4526_ = lean_ctor_get(v___x_4524_, 2);
v_postponed_4527_ = lean_ctor_get(v___x_4524_, 3);
v_diag_4528_ = lean_ctor_get(v___x_4524_, 4);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; 
v_unused_4538_ = lean_ctor_get(v___x_4524_, 0);
lean_dec(v_unused_4538_);
v___x_4530_ = v___x_4524_;
v_isShared_4531_ = v_isSharedCheck_4537_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_diag_4528_);
lean_inc(v_postponed_4527_);
lean_inc(v_zetaDeltaFVarIds_4526_);
lean_inc(v_cache_4525_);
lean_dec(v___x_4524_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4537_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v_snd_4523_);
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_snd_4523_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_cache_4525_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_zetaDeltaFVarIds_4526_);
lean_ctor_set(v_reuseFailAlloc_4536_, 3, v_postponed_4527_);
lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_diag_4528_);
v___x_4533_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = lean_st_ref_put(v___y_4515_, v___x_4533_);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v_fst_4522_);
return v___x_4535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg___boxed(lean_object* v_e_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4539_, v___y_4540_);
lean_dec(v___y_4540_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(lean_object* v_e_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4543_, v___y_4545_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___boxed(lean_object* v_e_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(v_e_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(lean_object* v_mvarId_4557_, lean_object* v_x_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4557_, v_x_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4564_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
v_a_4573_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4564_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4564_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4581_, lean_object* v_x_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4581_, v_x_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(lean_object* v_00_u03b1_4589_, lean_object* v_mvarId_4590_, lean_object* v_x_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4590_, v_x_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___boxed(lean_object* v_00_u03b1_4598_, lean_object* v_mvarId_4599_, lean_object* v_x_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(v_00_u03b1_4598_, v_mvarId_4599_, v_x_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(lean_object* v___x_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4624_; 
v___x_4613_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v___x_4607_, v___y_4609_);
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4624_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4624_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
uint8_t v___x_4618_; 
v___x_4618_ = l_Lean_Expr_hasSyntheticSorry(v_a_4614_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; 
lean_del_object(v___x_4616_);
v___x_4619_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_a_4614_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
return v___x_4619_;
}
else
{
lean_object* v___x_4620_; lean_object* v___x_4622_; 
lean_dec(v_a_4614_);
v___x_4620_ = lean_box(0);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4620_);
v___x_4622_ = v___x_4616_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed(lean_object* v___x_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(v___x_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(lean_object* v_mvarId_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v___x_4638_; lean_object* v___f_4639_; lean_object* v___x_4640_; 
lean_inc(v_mvarId_4632_);
v___x_4638_ = l_Lean_mkMVar(v_mvarId_4632_);
v___f_4639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4639_, 0, v___x_4638_);
v___x_4640_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4632_, v___f_4639_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___boxed(lean_object* v_mvarId_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(lean_object* v_mvarId_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg___boxed(lean_object* v_mvarId_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(v_mvarId_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
lean_dec(v_a_4659_);
lean_dec_ref(v_a_4658_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(lean_object* v_mvarId_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4662_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___boxed(lean_object* v_mvarId_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(v_mvarId_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v_zero_4688_; uint8_t v_isZero_4689_; 
v_zero_4688_ = lean_unsigned_to_nat(0u);
v_isZero_4689_ = lean_nat_dec_eq(v_a_4686_, v_zero_4688_);
if (v_isZero_4689_ == 0)
{
if (lean_obj_tag(v_a_4687_) == 6)
{
lean_object* v_body_4690_; lean_object* v_one_4691_; lean_object* v_n_4692_; 
v_body_4690_ = lean_ctor_get(v_a_4687_, 2);
v_one_4691_ = lean_unsigned_to_nat(1u);
v_n_4692_ = lean_nat_sub(v_a_4686_, v_one_4691_);
lean_dec(v_a_4686_);
v_a_4686_ = v_n_4692_;
v_a_4687_ = v_body_4690_;
goto _start;
}
else
{
lean_dec(v_a_4686_);
lean_inc_ref(v_a_4687_);
return v_a_4687_;
}
}
else
{
lean_dec(v_a_4686_);
lean_inc_ref(v_a_4687_);
return v_a_4687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody___boxed(lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v_a_4694_, v_a_4695_);
lean_dec_ref(v_a_4695_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(lean_object* v_mvarId_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; lean_object* v_mctx_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4700_ = lean_st_ref_get(v___y_4698_);
v_mctx_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc_ref(v_mctx_4701_);
lean_dec(v___x_4700_);
v___x_4702_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_4701_, v_mvarId_4697_);
lean_dec_ref(v_mctx_4701_);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg___boxed(lean_object* v_mvarId_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec(v_mvarId_4704_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(lean_object* v_mvarId_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4708_, v___y_4715_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___boxed(lean_object* v_mvarId_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(v_mvarId_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec(v_mvarId_4720_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(lean_object* v_mvarId_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; lean_object* v_mctx_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4735_ = lean_st_ref_get(v___y_4733_);
v_mctx_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc_ref(v_mctx_4736_);
lean_dec(v___x_4735_);
v___x_4737_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_4736_, v_mvarId_4732_);
lean_dec_ref(v_mctx_4736_);
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg___boxed(lean_object* v_mvarId_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec(v_mvarId_4739_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(lean_object* v_mvarId_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4743_, v___y_4750_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___boxed(lean_object* v_mvarId_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(v_mvarId_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec(v_mvarId_4755_);
return v_res_4766_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(lean_object* v___x_4767_, lean_object* v_x_4768_){
_start:
{
if (lean_obj_tag(v_x_4768_) == 0)
{
uint8_t v___x_4769_; 
v___x_4769_ = 1;
return v___x_4769_;
}
else
{
lean_object* v_head_4770_; lean_object* v_tail_4771_; lean_object* v_fst_4772_; lean_object* v_snd_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; uint8_t v___x_4778_; 
v_head_4770_ = lean_ctor_get(v_x_4768_, 0);
v_tail_4771_ = lean_ctor_get(v_x_4768_, 1);
v_fst_4772_ = lean_ctor_get(v_head_4770_, 0);
v_snd_4773_ = lean_ctor_get(v_head_4770_, 1);
v___x_4774_ = lean_unsigned_to_nat(1u);
v___x_4775_ = lean_nat_sub(v___x_4767_, v___x_4774_);
v___x_4776_ = lean_nat_sub(v___x_4775_, v_snd_4773_);
lean_dec(v___x_4775_);
v___x_4777_ = l_Lean_mkBVar(v___x_4776_);
v___x_4778_ = lean_expr_eqv(v_fst_4772_, v___x_4777_);
lean_dec_ref(v___x_4777_);
if (v___x_4778_ == 0)
{
return v___x_4778_;
}
else
{
v_x_4768_ = v_tail_4771_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0___boxed(lean_object* v___x_4780_, lean_object* v_x_4781_){
_start:
{
uint8_t v_res_4782_; lean_object* v_r_4783_; 
v_res_4782_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4780_, v_x_4781_);
lean_dec(v_x_4781_);
lean_dec(v___x_4780_);
v_r_4783_ = lean_box(v_res_4782_);
return v_r_4783_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(lean_object* v_k_4784_, lean_object* v_t_4785_){
_start:
{
if (lean_obj_tag(v_t_4785_) == 0)
{
lean_object* v_k_4786_; lean_object* v_l_4787_; lean_object* v_r_4788_; uint8_t v___x_4789_; 
v_k_4786_ = lean_ctor_get(v_t_4785_, 1);
v_l_4787_ = lean_ctor_get(v_t_4785_, 3);
v_r_4788_ = lean_ctor_get(v_t_4785_, 4);
v___x_4789_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4784_, v_k_4786_);
switch(v___x_4789_)
{
case 0:
{
v_t_4785_ = v_l_4787_;
goto _start;
}
case 1:
{
uint8_t v___x_4791_; 
v___x_4791_ = 1;
return v___x_4791_;
}
default: 
{
v_t_4785_ = v_r_4788_;
goto _start;
}
}
}
else
{
uint8_t v___x_4793_; 
v___x_4793_ = 0;
return v___x_4793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg___boxed(lean_object* v_k_4794_, lean_object* v_t_4795_){
_start:
{
uint8_t v_res_4796_; lean_object* v_r_4797_; 
v_res_4796_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4794_, v_t_4795_);
lean_dec(v_t_4795_);
lean_dec(v_k_4794_);
v_r_4797_ = lean_box(v_res_4796_);
return v_r_4797_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(lean_object* v_a_4798_, lean_object* v_as_4799_, size_t v_i_4800_, size_t v_stop_4801_){
_start:
{
uint8_t v___x_4802_; 
v___x_4802_ = lean_usize_dec_eq(v_i_4800_, v_stop_4801_);
if (v___x_4802_ == 0)
{
lean_object* v_fvars_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; uint8_t v___x_4806_; 
v_fvars_4803_ = lean_ctor_get(v_a_4798_, 0);
v___x_4804_ = lean_array_uget_borrowed(v_as_4799_, v_i_4800_);
v___x_4805_ = l_Lean_Expr_fvarId_x21(v___x_4804_);
v___x_4806_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v___x_4805_, v_fvars_4803_);
lean_dec(v___x_4805_);
if (v___x_4806_ == 0)
{
size_t v___x_4807_; size_t v___x_4808_; 
v___x_4807_ = ((size_t)1ULL);
v___x_4808_ = lean_usize_add(v_i_4800_, v___x_4807_);
v_i_4800_ = v___x_4808_;
goto _start;
}
else
{
return v___x_4806_;
}
}
else
{
uint8_t v___x_4810_; 
v___x_4810_ = 0;
return v___x_4810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3___boxed(lean_object* v_a_4811_, lean_object* v_as_4812_, lean_object* v_i_4813_, lean_object* v_stop_4814_){
_start:
{
size_t v_i_boxed_4815_; size_t v_stop_boxed_4816_; uint8_t v_res_4817_; lean_object* v_r_4818_; 
v_i_boxed_4815_ = lean_unbox_usize(v_i_4813_);
lean_dec(v_i_4813_);
v_stop_boxed_4816_ = lean_unbox_usize(v_stop_4814_);
lean_dec(v_stop_4814_);
v_res_4817_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4811_, v_as_4812_, v_i_boxed_4815_, v_stop_boxed_4816_);
lean_dec_ref(v_as_4812_);
lean_dec_ref(v_a_4811_);
v_r_4818_ = lean_box(v_res_4817_);
return v_r_4818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_4819_; lean_object* v_dummy_4820_; 
v___x_4819_ = lean_box(0);
v_dummy_4820_ = l_Lean_Expr_sort___override(v___x_4819_);
return v_dummy_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_mvarId_4821_, lean_object* v_proof_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v_p_4834_; lean_object* v_proof_4837_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v___x_4960_; 
v_proof_4837_ = l_Lean_Expr_headBeta(v_proof_4822_);
v___x_4960_ = l_Lean_Expr_getAppFn(v_proof_4837_);
if (lean_obj_tag(v___x_4960_) == 2)
{
lean_object* v_mvarId_4961_; lean_object* v___x_4962_; 
v_mvarId_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_mvarId_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4961_, v_a_4829_);
lean_dec(v_mvarId_4961_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
if (lean_obj_tag(v_a_4963_) == 1)
{
lean_object* v_val_4964_; lean_object* v_dummy_4965_; lean_object* v_nargs_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_val_4964_ = lean_ctor_get(v_a_4963_, 0);
lean_inc(v_val_4964_);
lean_dec_ref_known(v_a_4963_, 1);
v_dummy_4965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4966_ = l_Lean_Expr_getAppNumArgs(v_proof_4837_);
lean_inc(v_nargs_4966_);
v___x_4967_ = lean_mk_array(v_nargs_4966_, v_dummy_4965_);
v___x_4968_ = lean_unsigned_to_nat(1u);
v___x_4969_ = lean_nat_sub(v_nargs_4966_, v___x_4968_);
lean_dec(v_nargs_4966_);
v___x_4970_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_proof_4837_, v___x_4967_, v___x_4969_);
v___x_4971_ = l_Lean_Expr_beta(v_val_4964_, v___x_4970_);
v_proof_4822_ = v___x_4971_;
goto _start;
}
else
{
lean_dec(v_a_4963_);
v___y_4915_ = v_a_4823_;
v___y_4916_ = v_a_4824_;
v___y_4917_ = v_a_4825_;
v___y_4918_ = v_a_4826_;
v___y_4919_ = v_a_4827_;
v___y_4920_ = v_a_4828_;
v___y_4921_ = v_a_4829_;
v___y_4922_ = v_a_4830_;
v___y_4923_ = v_a_4831_;
goto v___jp_4914_;
}
}
else
{
lean_dec_ref(v_proof_4837_);
lean_dec(v_mvarId_4821_);
return v___x_4962_;
}
}
else
{
lean_dec_ref(v___x_4960_);
v___y_4915_ = v_a_4823_;
v___y_4916_ = v_a_4824_;
v___y_4917_ = v_a_4825_;
v___y_4918_ = v_a_4826_;
v___y_4919_ = v_a_4827_;
v___y_4920_ = v_a_4828_;
v___y_4921_ = v_a_4829_;
v___y_4922_ = v_a_4830_;
v___y_4923_ = v_a_4831_;
goto v___jp_4914_;
}
v___jp_4833_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4835_, 0, v_p_4834_);
v___x_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
return v___x_4836_;
}
v___jp_4838_:
{
if (lean_obj_tag(v_proof_4837_) == 6)
{
lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4848_ = l_Lean_Expr_getNumHeadLambdas(v_proof_4837_);
lean_inc(v___x_4848_);
v___x_4849_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v___x_4848_, v_proof_4837_);
lean_dec_ref_known(v_proof_4837_, 3);
v___x_4850_ = l_Lean_Expr_hasLooseBVars(v___x_4849_);
if (v___x_4850_ == 0)
{
lean_dec(v___x_4848_);
v_proof_4822_ = v___x_4849_;
v_a_4823_ = v___y_4839_;
v_a_4824_ = v___y_4840_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
goto _start;
}
else
{
lean_object* v___x_4852_; 
v___x_4852_ = l_Lean_Expr_getAppFn(v___x_4849_);
if (lean_obj_tag(v___x_4852_) == 2)
{
lean_object* v_mvarId_4853_; lean_object* v_dummy_4854_; lean_object* v_nargs_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v_mvarId_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_mvarId_4853_);
lean_dec_ref_known(v___x_4852_, 1);
v_dummy_4854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4855_ = l_Lean_Expr_getAppNumArgs(v___x_4849_);
lean_inc(v_nargs_4855_);
v___x_4856_ = lean_mk_array(v_nargs_4855_, v_dummy_4854_);
v___x_4857_ = lean_unsigned_to_nat(1u);
v___x_4858_ = lean_nat_sub(v_nargs_4855_, v___x_4857_);
lean_dec(v_nargs_4855_);
v___x_4859_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_4849_, v___x_4856_, v___x_4858_);
v___x_4860_ = lean_array_get_size(v___x_4859_);
v___x_4861_ = lean_nat_dec_eq(v___x_4860_, v___x_4848_);
if (v___x_4861_ == 0)
{
lean_object* v___x_4862_; 
lean_dec_ref(v___x_4859_);
lean_dec(v_mvarId_4853_);
lean_dec(v___x_4848_);
v___x_4862_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4821_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4862_;
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; 
v___x_4863_ = lean_array_to_list(v___x_4859_);
v___x_4864_ = lean_unsigned_to_nat(0u);
v___x_4865_ = l_List_zipIdxTR___redArg(v___x_4863_, v___x_4864_);
v___x_4866_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4848_, v___x_4865_);
lean_dec(v___x_4865_);
if (v___x_4866_ == 0)
{
lean_object* v___x_4867_; 
lean_dec(v_mvarId_4853_);
lean_dec(v___x_4848_);
v___x_4867_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4821_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4867_;
}
else
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4853_, v___y_4845_);
lean_dec(v_mvarId_4853_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref_known(v___x_4868_, 1);
if (lean_obj_tag(v_a_4869_) == 1)
{
lean_object* v_val_4870_; lean_object* v_fvars_4871_; lean_object* v_mvarIdPending_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v_val_4870_ = lean_ctor_get(v_a_4869_, 0);
lean_inc(v_val_4870_);
lean_dec_ref_known(v_a_4869_, 1);
v_fvars_4871_ = lean_ctor_get(v_val_4870_, 0);
lean_inc_ref(v_fvars_4871_);
v_mvarIdPending_4872_ = lean_ctor_get(v_val_4870_, 1);
lean_inc(v_mvarIdPending_4872_);
lean_dec(v_val_4870_);
v___x_4873_ = lean_array_get_size(v_fvars_4871_);
v___x_4874_ = lean_nat_dec_eq(v___x_4873_, v___x_4848_);
lean_dec(v___x_4848_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; 
lean_dec(v_mvarIdPending_4872_);
lean_dec_ref(v_fvars_4871_);
v___x_4875_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4821_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4875_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = l_Lean_mkMVar(v_mvarIdPending_4872_);
lean_inc_ref(v___x_4876_);
v___x_4877_ = l_Lean_Meta_Grind_getProofInfo(v___x_4876_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4893_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4880_ = v___x_4877_;
v_isShared_4881_ = v_isSharedCheck_4893_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4893_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
uint8_t v___x_4882_; 
v___x_4882_ = lean_nat_dec_lt(v___x_4864_, v___x_4873_);
if (v___x_4882_ == 0)
{
lean_del_object(v___x_4880_);
lean_dec(v_a_4878_);
lean_dec_ref(v_fvars_4871_);
v_proof_4822_ = v___x_4876_;
v_a_4823_ = v___y_4839_;
v_a_4824_ = v___y_4840_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
goto _start;
}
else
{
if (v___x_4882_ == 0)
{
lean_del_object(v___x_4880_);
lean_dec(v_a_4878_);
lean_dec_ref(v_fvars_4871_);
v_proof_4822_ = v___x_4876_;
v_a_4823_ = v___y_4839_;
v_a_4824_ = v___y_4840_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
goto _start;
}
else
{
size_t v___x_4885_; size_t v___x_4886_; uint8_t v___x_4887_; 
v___x_4885_ = ((size_t)0ULL);
v___x_4886_ = lean_usize_of_nat(v___x_4873_);
v___x_4887_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4878_, v_fvars_4871_, v___x_4885_, v___x_4886_);
lean_dec_ref(v_fvars_4871_);
lean_dec(v_a_4878_);
if (v___x_4887_ == 0)
{
lean_del_object(v___x_4880_);
v_proof_4822_ = v___x_4876_;
v_a_4823_ = v___y_4839_;
v_a_4824_ = v___y_4840_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
goto _start;
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
lean_dec_ref(v___x_4876_);
lean_dec(v_mvarId_4821_);
v___x_4889_ = lean_box(0);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4889_);
v___x_4891_ = v___x_4880_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
}
else
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
lean_dec_ref(v___x_4876_);
lean_dec_ref(v_fvars_4871_);
lean_dec(v_mvarId_4821_);
v_a_4894_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4896_ = v___x_4877_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4877_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4894_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
}
else
{
lean_object* v___x_4902_; 
lean_dec(v_a_4869_);
lean_dec(v___x_4848_);
v___x_4902_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4821_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4902_;
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v___x_4848_);
lean_dec(v_mvarId_4821_);
v_a_4903_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4868_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4868_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
}
}
else
{
lean_object* v___x_4911_; 
lean_dec_ref(v___x_4852_);
lean_dec_ref(v___x_4849_);
lean_dec(v___x_4848_);
v___x_4911_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4821_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4911_;
}
}
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
lean_dec_ref(v_proof_4837_);
lean_dec(v_mvarId_4821_);
v___x_4912_ = lean_box(0);
v___x_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
return v___x_4913_;
}
}
v___jp_4914_:
{
lean_object* v___x_4924_; 
lean_inc_ref(v_proof_4837_);
v___x_4924_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4837_, v___y_4921_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4951_; 
v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4927_ = v___x_4924_;
v_isShared_4928_ = v_isSharedCheck_4951_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4924_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4951_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; uint8_t v___x_4930_; 
v___x_4929_ = l_Lean_Expr_cleanupAnnotations(v_a_4925_);
lean_dec(v_a_4925_);
v___x_4930_ = l_Lean_Expr_isApp(v___x_4929_);
if (v___x_4930_ == 0)
{
lean_dec_ref(v___x_4929_);
lean_del_object(v___x_4927_);
v___y_4839_ = v___y_4915_;
v___y_4840_ = v___y_4916_;
v___y_4841_ = v___y_4917_;
v___y_4842_ = v___y_4918_;
v___y_4843_ = v___y_4919_;
v___y_4844_ = v___y_4920_;
v___y_4845_ = v___y_4921_;
v___y_4846_ = v___y_4922_;
v___y_4847_ = v___y_4923_;
goto v___jp_4838_;
}
else
{
lean_object* v___x_4931_; uint8_t v___x_4932_; 
v___x_4931_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4929_);
v___x_4932_ = l_Lean_Expr_isApp(v___x_4931_);
if (v___x_4932_ == 0)
{
lean_dec_ref(v___x_4931_);
lean_dec_ref(v___x_4929_);
lean_del_object(v___x_4927_);
v___y_4839_ = v___y_4915_;
v___y_4840_ = v___y_4916_;
v___y_4841_ = v___y_4917_;
v___y_4842_ = v___y_4918_;
v___y_4843_ = v___y_4919_;
v___y_4844_ = v___y_4920_;
v___y_4845_ = v___y_4921_;
v___y_4846_ = v___y_4922_;
v___y_4847_ = v___y_4923_;
goto v___jp_4838_;
}
else
{
lean_object* v_arg_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; uint8_t v___x_4936_; 
v_arg_4933_ = lean_ctor_get(v___x_4929_, 1);
lean_inc_ref(v_arg_4933_);
lean_dec_ref(v___x_4929_);
v___x_4934_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4931_);
v___x_4935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4936_ = l_Lean_Expr_isConstOf(v___x_4934_, v___x_4935_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; uint8_t v___x_4938_; 
lean_dec_ref(v___x_4931_);
lean_del_object(v___x_4927_);
v___x_4937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4938_ = l_Lean_Expr_isConstOf(v___x_4934_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; uint8_t v___x_4940_; 
v___x_4939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4940_ = l_Lean_Expr_isConstOf(v___x_4934_, v___x_4939_);
lean_dec_ref(v___x_4934_);
if (v___x_4940_ == 0)
{
lean_dec_ref(v_arg_4933_);
v___y_4839_ = v___y_4915_;
v___y_4840_ = v___y_4916_;
v___y_4841_ = v___y_4917_;
v___y_4842_ = v___y_4918_;
v___y_4843_ = v___y_4919_;
v___y_4844_ = v___y_4920_;
v___y_4845_ = v___y_4921_;
v___y_4846_ = v___y_4922_;
v___y_4847_ = v___y_4923_;
goto v___jp_4838_;
}
else
{
lean_dec_ref(v_proof_4837_);
lean_dec(v_mvarId_4821_);
v_p_4834_ = v_arg_4933_;
goto v___jp_4833_;
}
}
else
{
lean_dec_ref(v___x_4934_);
lean_dec_ref(v_proof_4837_);
lean_dec(v_mvarId_4821_);
v_p_4834_ = v_arg_4933_;
goto v___jp_4833_;
}
}
else
{
lean_object* v_arg_4941_; uint8_t v___x_4942_; 
lean_dec_ref(v___x_4934_);
lean_dec_ref(v_proof_4837_);
lean_dec(v_mvarId_4821_);
v_arg_4941_ = lean_ctor_get(v___x_4931_, 1);
lean_inc_ref(v_arg_4941_);
lean_dec_ref(v___x_4931_);
v___x_4942_ = l_Lean_Expr_isFalse(v_arg_4941_);
lean_dec_ref(v_arg_4941_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; lean_object* v___x_4945_; 
lean_dec_ref(v_arg_4933_);
v___x_4943_ = lean_box(0);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v___x_4943_);
v___x_4945_ = v___x_4927_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4943_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4947_, 0, v_arg_4933_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v___x_4947_);
v___x_4949_ = v___x_4927_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec_ref(v_proof_4837_);
lean_dec(v_mvarId_4821_);
v_a_4952_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4924_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4924_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_mvarId_4973_, lean_object* v_proof_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_4973_, v_proof_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
lean_dec(v_a_4983_);
lean_dec_ref(v_a_4982_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
return v_res_4985_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(lean_object* v_00_u03b2_4986_, lean_object* v_k_4987_, lean_object* v_t_4988_){
_start:
{
uint8_t v___x_4989_; 
v___x_4989_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4987_, v_t_4988_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_4990_, lean_object* v_k_4991_, lean_object* v_t_4992_){
_start:
{
uint8_t v_res_4993_; lean_object* v_r_4994_; 
v_res_4993_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(v_00_u03b2_4990_, v_k_4991_, v_t_4992_);
lean_dec(v_t_4992_);
lean_dec(v_k_4991_);
v_r_4994_ = lean_box(v_res_4993_);
return v_r_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(lean_object* v_x_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v___x_5006_; 
lean_inc(v___y_5000_);
lean_inc_ref(v___y_4999_);
lean_inc(v___y_4998_);
lean_inc_ref(v___y_4997_);
lean_inc(v___y_4996_);
v___x_5006_ = lean_apply_10(v_x_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, lean_box(0));
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(v_x_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
lean_dec(v___y_5012_);
lean_dec_ref(v___y_5011_);
lean_dec(v___y_5010_);
lean_dec_ref(v___y_5009_);
lean_dec(v___y_5008_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_mvarId_5019_, lean_object* v_x_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v___f_5031_; lean_object* v___x_5032_; 
lean_inc(v___y_5025_);
lean_inc_ref(v___y_5024_);
lean_inc(v___y_5023_);
lean_inc_ref(v___y_5022_);
lean_inc(v___y_5021_);
v___f_5031_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5031_, 0, v_x_5020_);
lean_closure_set(v___f_5031_, 1, v___y_5021_);
lean_closure_set(v___f_5031_, 2, v___y_5022_);
lean_closure_set(v___f_5031_, 3, v___y_5023_);
lean_closure_set(v___f_5031_, 4, v___y_5024_);
lean_closure_set(v___f_5031_, 5, v___y_5025_);
v___x_5032_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5019_, v___f_5031_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5032_) == 0)
{
return v___x_5032_;
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5032_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5032_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_5041_, lean_object* v_x_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5041_, v_x_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
lean_dec(v___y_5043_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_00_u03b1_5054_, lean_object* v_mvarId_5055_, lean_object* v_x_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v___x_5067_; 
v___x_5067_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5055_, v_x_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_00_u03b1_5068_, lean_object* v_mvarId_5069_, lean_object* v_x_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_00_u03b1_5068_, v_mvarId_5069_, v_x_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5078_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v___y_5075_);
lean_dec_ref(v___y_5074_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_5082_, lean_object* v_mvarId_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v___x_5094_; 
lean_inc_ref(v___x_5082_);
v___x_5094_ = l_Lean_Meta_Grind_getProofInfo(v___x_5082_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5107_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5097_ = v___x_5094_;
v_isShared_5098_ = v_isSharedCheck_5107_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5094_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5107_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
uint8_t v_hasSorry_5104_; 
v_hasSorry_5104_ = lean_ctor_get_uint8(v_a_5095_, sizeof(void*)*1);
if (v_hasSorry_5104_ == 0)
{
uint8_t v_hasUnassigned_5105_; 
v_hasUnassigned_5105_ = lean_ctor_get_uint8(v_a_5095_, sizeof(void*)*1 + 1);
lean_dec(v_a_5095_);
if (v_hasUnassigned_5105_ == 0)
{
lean_object* v___x_5106_; 
lean_del_object(v___x_5097_);
v___x_5106_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_5083_, v___x_5082_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
return v___x_5106_;
}
else
{
lean_dec(v_mvarId_5083_);
lean_dec_ref(v___x_5082_);
goto v___jp_5099_;
}
}
else
{
lean_dec(v_a_5095_);
lean_dec(v_mvarId_5083_);
lean_dec_ref(v___x_5082_);
goto v___jp_5099_;
}
v___jp_5099_:
{
lean_object* v___x_5100_; lean_object* v___x_5102_; 
v___x_5100_ = lean_box(0);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v___x_5100_);
v___x_5102_ = v___x_5097_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5100_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
lean_dec(v_mvarId_5083_);
lean_dec_ref(v___x_5082_);
v_a_5108_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_5094_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5094_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_5116_, lean_object* v_mvarId_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_5116_, v_mvarId_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v___x_5140_; lean_object* v___f_5141_; lean_object* v___x_5142_; 
lean_inc_n(v_mvarId_5129_, 2);
v___x_5140_ = l_Lean_mkMVar(v_mvarId_5129_);
v___f_5141_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5141_, 0, v___x_5140_);
lean_closure_set(v___f_5141_, 1, v_mvarId_5129_);
v___x_5142_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5129_, v___f_5141_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
lean_dec(v_a_5144_);
return v_res_5154_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_5176_){
_start:
{
if (lean_obj_tag(v_x_5176_) == 0)
{
uint8_t v___x_5177_; 
v___x_5177_ = 1;
return v___x_5177_;
}
else
{
lean_object* v_head_5178_; lean_object* v_tail_5179_; lean_object* v___x_5180_; uint8_t v___x_5181_; 
v_head_5178_ = lean_ctor_get(v_x_5176_, 0);
lean_inc_n(v_head_5178_, 2);
v_tail_5179_ = lean_ctor_get(v_x_5176_, 1);
lean_inc(v_tail_5179_);
lean_dec_ref_known(v_x_5176_, 2);
v___x_5180_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_5181_ = l_Lean_Syntax_isOfKind(v_head_5178_, v___x_5180_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; uint8_t v___x_5183_; 
v___x_5182_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_5178_);
v___x_5183_ = l_Lean_Syntax_isOfKind(v_head_5178_, v___x_5182_);
if (v___x_5183_ == 0)
{
lean_dec(v_head_5178_);
v_x_5176_ = v_tail_5179_;
goto _start;
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; uint8_t v___x_5188_; 
v___x_5185_ = lean_unsigned_to_nat(1u);
v___x_5186_ = l_Lean_Syntax_getArg(v_head_5178_, v___x_5185_);
lean_dec(v_head_5178_);
v___x_5187_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5188_ = l_Lean_Syntax_isOfKind(v___x_5186_, v___x_5187_);
if (v___x_5188_ == 0)
{
v_x_5176_ = v_tail_5179_;
goto _start;
}
else
{
lean_dec(v_tail_5179_);
return v___x_5181_;
}
}
}
else
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5190_ = lean_unsigned_to_nat(3u);
v___x_5191_ = l_Lean_Syntax_getArg(v_head_5178_, v___x_5190_);
lean_dec(v_head_5178_);
v___x_5192_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5193_ = l_Lean_Syntax_isOfKind(v___x_5191_, v___x_5192_);
if (v___x_5193_ == 0)
{
v_x_5176_ = v_tail_5179_;
goto _start;
}
else
{
uint8_t v___x_5195_; 
lean_dec(v_tail_5179_);
v___x_5195_ = 0;
return v___x_5195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_5196_){
_start:
{
uint8_t v_res_5197_; lean_object* v_r_5198_; 
v_res_5197_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_5196_);
v_r_5198_ = lean_box(v_res_5197_);
return v_r_5198_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_5199_){
_start:
{
uint8_t v___x_5200_; 
v___x_5200_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_5199_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_5201_){
_start:
{
uint8_t v_res_5202_; lean_object* v_r_5203_; 
v_res_5202_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_5201_);
v_r_5203_ = lean_box(v_res_5202_);
return v_r_5203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_5219_, lean_object* v_a_5220_){
_start:
{
if (lean_obj_tag(v_seq_5219_) == 0)
{
lean_object* v_ref_5222_; uint8_t v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_ref_5222_ = lean_ctor_get(v_a_5220_, 2);
v___x_5223_ = 0;
v___x_5224_ = l_Lean_SourceInfo_fromRef(v_ref_5222_, v___x_5223_);
v___x_5225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_5226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_5224_);
v___x_5227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5224_);
lean_ctor_set(v___x_5227_, 1, v___x_5225_);
v___x_5228_ = l_Lean_Syntax_node1(v___x_5224_, v___x_5226_, v___x_5227_);
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5228_);
return v___x_5229_;
}
else
{
lean_object* v_tail_5230_; 
v_tail_5230_ = lean_ctor_get(v_seq_5219_, 1);
if (lean_obj_tag(v_tail_5230_) == 0)
{
lean_object* v_head_5231_; lean_object* v___x_5232_; 
v_head_5231_ = lean_ctor_get(v_seq_5219_, 0);
lean_inc(v_head_5231_);
lean_dec_ref_known(v_seq_5219_, 2);
v___x_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5232_, 0, v_head_5231_);
return v___x_5232_;
}
else
{
lean_object* v_head_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5255_; 
lean_inc(v_tail_5230_);
v_head_5233_ = lean_ctor_get(v_seq_5219_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_seq_5219_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; 
v_unused_5256_ = lean_ctor_get(v_seq_5219_, 1);
lean_dec(v_unused_5256_);
v___x_5235_ = v_seq_5219_;
v_isShared_5236_ = v_isSharedCheck_5255_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_head_5233_);
lean_dec(v_seq_5219_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5255_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5237_; lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5254_; 
v___x_5237_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_5230_, v_a_5220_);
v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5254_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5254_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v_ref_5242_; uint8_t v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5248_; 
v_ref_5242_ = lean_ctor_get(v_a_5220_, 2);
v___x_5243_ = 0;
v___x_5244_ = l_Lean_SourceInfo_fromRef(v_ref_5242_, v___x_5243_);
v___x_5245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5244_);
if (v_isShared_5236_ == 0)
{
lean_ctor_set_tag(v___x_5235_, 2);
lean_ctor_set(v___x_5235_, 1, v___x_5246_);
lean_ctor_set(v___x_5235_, 0, v___x_5244_);
v___x_5248_ = v___x_5235_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5244_);
lean_ctor_set(v_reuseFailAlloc_5253_, 1, v___x_5246_);
v___x_5248_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
v___x_5249_ = l_Lean_Syntax_node3(v___x_5244_, v___x_5245_, v_head_5233_, v___x_5248_, v_a_5238_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v___x_5249_);
v___x_5251_ = v___x_5240_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5257_, v_a_5258_);
lean_dec_ref(v_a_5258_);
return v_res_5260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v___x_5265_; 
v___x_5265_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5261_, v_a_5262_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_){
_start:
{
lean_object* v_res_5270_; 
v_res_5270_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_5266_, v_a_5267_, v_a_5268_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
return v_res_5270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_5271_, lean_object* v_seq_5272_, lean_object* v_a_5273_){
_start:
{
if (lean_obj_tag(v_seq_5272_) == 0)
{
lean_object* v___x_5275_; 
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v_cases_5271_);
return v___x_5275_;
}
else
{
lean_object* v___x_5276_; lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5291_; 
v___x_5276_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5272_, v_a_5273_);
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5291_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5291_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_ref_5281_; uint8_t v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5289_; 
v_ref_5281_ = lean_ctor_get(v_a_5273_, 2);
v___x_5282_ = 0;
v___x_5283_ = l_Lean_SourceInfo_fromRef(v_ref_5281_, v___x_5282_);
v___x_5284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5283_);
v___x_5286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5286_, 0, v___x_5283_);
lean_ctor_set(v___x_5286_, 1, v___x_5285_);
v___x_5287_ = l_Lean_Syntax_node3(v___x_5283_, v___x_5284_, v_cases_5271_, v___x_5286_, v_a_5277_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 0, v___x_5287_);
v___x_5289_ = v___x_5279_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v___x_5287_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_5292_, lean_object* v_seq_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5292_, v_seq_5293_, v_a_5294_);
lean_dec_ref(v_a_5294_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_5297_, lean_object* v_seq_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_){
_start:
{
lean_object* v___x_5302_; 
v___x_5302_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5297_, v_seq_5298_, v_a_5299_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_5303_, lean_object* v_seq_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_){
_start:
{
lean_object* v_res_5308_; 
v_res_5308_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_5303_, v_seq_5304_, v_a_5305_, v_a_5306_);
lean_dec(v_a_5306_);
lean_dec_ref(v_a_5305_);
return v_res_5308_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_5309_, lean_object* v_x_5310_){
_start:
{
if (lean_obj_tag(v_x_5309_) == 0)
{
if (lean_obj_tag(v_x_5310_) == 0)
{
uint8_t v___x_5311_; 
v___x_5311_ = 1;
return v___x_5311_;
}
else
{
uint8_t v___x_5312_; 
v___x_5312_ = 0;
return v___x_5312_;
}
}
else
{
if (lean_obj_tag(v_x_5310_) == 0)
{
uint8_t v___x_5313_; 
v___x_5313_ = 0;
return v___x_5313_;
}
else
{
lean_object* v_head_5314_; lean_object* v_tail_5315_; lean_object* v_head_5316_; lean_object* v_tail_5317_; uint8_t v___x_5318_; 
v_head_5314_ = lean_ctor_get(v_x_5309_, 0);
v_tail_5315_ = lean_ctor_get(v_x_5309_, 1);
v_head_5316_ = lean_ctor_get(v_x_5310_, 0);
v_tail_5317_ = lean_ctor_get(v_x_5310_, 1);
v___x_5318_ = l_Lean_Syntax_structEq(v_head_5314_, v_head_5316_);
if (v___x_5318_ == 0)
{
return v___x_5318_;
}
else
{
v_x_5309_ = v_tail_5315_;
v_x_5310_ = v_tail_5317_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_5320_, lean_object* v_x_5321_){
_start:
{
uint8_t v_res_5322_; lean_object* v_r_5323_; 
v_res_5322_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_5320_, v_x_5321_);
lean_dec(v_x_5321_);
lean_dec(v_x_5320_);
v_r_5323_ = lean_box(v_res_5322_);
return v_r_5323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_5324_, lean_object* v___x_5325_, lean_object* v_as_5326_, size_t v_i_5327_, size_t v_stop_5328_){
_start:
{
uint8_t v___x_5333_; 
v___x_5333_ = lean_usize_dec_eq(v_i_5327_, v_stop_5328_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; uint8_t v___x_5335_; 
v___x_5334_ = lean_array_uget_borrowed(v_as_5326_, v_i_5327_);
v___x_5335_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_5334_, v_alt_5324_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; uint8_t v___x_5337_; 
v___x_5336_ = lean_unsigned_to_nat(0u);
v___x_5337_ = lean_nat_dec_lt(v___x_5336_, v___x_5325_);
if (v___x_5337_ == 0)
{
goto v___jp_5329_;
}
else
{
return v___x_5337_;
}
}
else
{
goto v___jp_5329_;
}
}
else
{
uint8_t v___x_5338_; 
v___x_5338_ = 0;
return v___x_5338_;
}
v___jp_5329_:
{
size_t v___x_5330_; size_t v___x_5331_; 
v___x_5330_ = ((size_t)1ULL);
v___x_5331_ = lean_usize_add(v_i_5327_, v___x_5330_);
v_i_5327_ = v___x_5331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_5339_, lean_object* v___x_5340_, lean_object* v_as_5341_, lean_object* v_i_5342_, lean_object* v_stop_5343_){
_start:
{
size_t v_i_boxed_5344_; size_t v_stop_boxed_5345_; uint8_t v_res_5346_; lean_object* v_r_5347_; 
v_i_boxed_5344_ = lean_unbox_usize(v_i_5342_);
lean_dec(v_i_5342_);
v_stop_boxed_5345_ = lean_unbox_usize(v_stop_5343_);
lean_dec(v_stop_5343_);
v_res_5346_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5339_, v___x_5340_, v_as_5341_, v_i_boxed_5344_, v_stop_boxed_5345_);
lean_dec_ref(v_as_5341_);
lean_dec(v___x_5340_);
lean_dec(v_alt_5339_);
v_r_5347_ = lean_box(v_res_5346_);
return v_r_5347_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_5348_){
_start:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; uint8_t v___x_5351_; 
v___x_5349_ = lean_unsigned_to_nat(0u);
v___x_5350_ = lean_array_get_size(v_alts_5348_);
v___x_5351_ = lean_nat_dec_lt(v___x_5349_, v___x_5350_);
if (v___x_5351_ == 0)
{
uint8_t v___x_5352_; 
v___x_5352_ = 1;
return v___x_5352_;
}
else
{
lean_object* v_alt_5353_; uint8_t v___x_5354_; 
v_alt_5353_ = lean_array_fget_borrowed(v_alts_5348_, v___x_5349_);
lean_inc(v_alt_5353_);
v___x_5354_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_5353_);
if (v___x_5354_ == 0)
{
return v___x_5354_;
}
else
{
if (v___x_5351_ == 0)
{
return v___x_5351_;
}
else
{
size_t v___x_5355_; size_t v___x_5356_; uint8_t v___x_5357_; 
v___x_5355_ = ((size_t)0ULL);
v___x_5356_ = lean_usize_of_nat(v___x_5350_);
v___x_5357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5353_, v___x_5350_, v_alts_5348_, v___x_5355_, v___x_5356_);
if (v___x_5357_ == 0)
{
return v___x_5351_;
}
else
{
uint8_t v___x_5358_; 
v___x_5358_ = 0;
return v___x_5358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_5359_){
_start:
{
uint8_t v_res_5360_; lean_object* v_r_5361_; 
v_res_5360_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5359_);
lean_dec_ref(v_alts_5359_);
v_r_5361_ = lean_box(v_res_5360_);
return v_r_5361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_5369_){
_start:
{
if (lean_obj_tag(v_alt_5369_) == 1)
{
lean_object* v_tail_5370_; 
v_tail_5370_ = lean_ctor_get(v_alt_5369_, 1);
if (lean_obj_tag(v_tail_5370_) == 0)
{
lean_object* v_head_5371_; lean_object* v___x_5372_; uint8_t v___x_5373_; 
v_head_5371_ = lean_ctor_get(v_alt_5369_, 0);
lean_inc(v_head_5371_);
lean_dec_ref_known(v_alt_5369_, 2);
v___x_5372_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_5373_ = l_Lean_Syntax_isOfKind(v_head_5371_, v___x_5372_);
return v___x_5373_;
}
else
{
uint8_t v___x_5374_; 
lean_dec_ref_known(v_alt_5369_, 2);
v___x_5374_ = 0;
return v___x_5374_;
}
}
else
{
uint8_t v___x_5375_; 
lean_dec(v_alt_5369_);
v___x_5375_ = 0;
return v___x_5375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_5376_){
_start:
{
uint8_t v_res_5377_; lean_object* v_r_5378_; 
v_res_5377_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_5376_);
v_r_5378_ = lean_box(v_res_5377_);
return v_r_5378_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_5379_, lean_object* v_x_5380_, lean_object* v___y_5381_){
_start:
{
if (lean_obj_tag(v_x_5379_) == 0)
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = l_List_reverse___redArg(v_x_5380_);
v___x_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5383_);
return v___x_5384_;
}
else
{
lean_object* v_head_5385_; lean_object* v_tail_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5404_; 
v_head_5385_ = lean_ctor_get(v_x_5379_, 0);
v_tail_5386_ = lean_ctor_get(v_x_5379_, 1);
v_isSharedCheck_5404_ = !lean_is_exclusive(v_x_5379_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5388_ = v_x_5379_;
v_isShared_5389_ = v_isSharedCheck_5404_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_tail_5386_);
lean_inc(v_head_5385_);
lean_dec(v_x_5379_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5404_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5390_; 
v___x_5390_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_5385_, v___y_5381_);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; lean_object* v___x_5393_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
lean_inc(v_a_5391_);
lean_dec_ref_known(v___x_5390_, 1);
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 1, v_x_5380_);
lean_ctor_set(v___x_5388_, 0, v_a_5391_);
v___x_5393_ = v___x_5388_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5391_);
lean_ctor_set(v_reuseFailAlloc_5395_, 1, v_x_5380_);
v___x_5393_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
v_x_5379_ = v_tail_5386_;
v_x_5380_ = v___x_5393_;
goto _start;
}
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_del_object(v___x_5388_);
lean_dec(v_tail_5386_);
lean_dec(v_x_5380_);
v_a_5396_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5390_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5390_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_5405_, lean_object* v_x_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v_res_5409_; 
v_res_5409_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5405_, v_x_5406_, v___y_5407_);
lean_dec_ref(v___y_5407_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_5410_, lean_object* v_alts_5411_, uint8_t v_compress_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_seq_5417_; 
if (v_compress_5412_ == 0)
{
goto v___jp_5420_;
}
else
{
uint8_t v___x_5430_; 
v___x_5430_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5411_);
if (v___x_5430_ == 0)
{
goto v___jp_5420_;
}
else
{
lean_object* v___x_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; 
v___x_5431_ = lean_unsigned_to_nat(0u);
v___x_5432_ = lean_array_get_size(v_alts_5411_);
v___x_5433_ = lean_nat_dec_lt(v___x_5431_, v___x_5432_);
if (v___x_5433_ == 0)
{
lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; 
lean_dec_ref(v_alts_5411_);
v___x_5434_ = lean_box(0);
v___x_5435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5435_, 0, v_cases_5410_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5436_, 0, v___x_5435_);
return v___x_5436_;
}
else
{
lean_object* v___x_5437_; lean_object* v_firstAlt_5438_; uint8_t v___x_5439_; 
v___x_5437_ = lean_box(0);
v_firstAlt_5438_ = lean_array_get(v___x_5437_, v_alts_5411_, v___x_5431_);
lean_dec_ref(v_alts_5411_);
lean_inc(v_firstAlt_5438_);
v___x_5439_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_5438_);
if (v___x_5439_ == 0)
{
lean_object* v___x_5440_; lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5449_; 
v___x_5440_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5410_, v_firstAlt_5438_, v_a_5413_);
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5443_ = v___x_5440_;
v_isShared_5444_ = v_isSharedCheck_5449_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5440_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5449_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5445_; lean_object* v___x_5447_; 
v___x_5445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5445_, 0, v_a_5441_);
lean_ctor_set(v___x_5445_, 1, v___x_5437_);
if (v_isShared_5444_ == 0)
{
lean_ctor_set(v___x_5443_, 0, v___x_5445_);
v___x_5447_ = v___x_5443_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
else
{
lean_object* v___x_5450_; 
lean_dec(v_cases_5410_);
v___x_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5450_, 0, v_firstAlt_5438_);
return v___x_5450_;
}
}
}
}
v___jp_5416_:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5418_, 0, v_cases_5410_);
lean_ctor_set(v___x_5418_, 1, v_seq_5417_);
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
return v___x_5419_;
}
v___jp_5420_:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; uint8_t v___x_5423_; 
v___x_5421_ = lean_array_get_size(v_alts_5411_);
v___x_5422_ = lean_unsigned_to_nat(1u);
v___x_5423_ = lean_nat_dec_eq(v___x_5421_, v___x_5422_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5424_ = lean_array_to_list(v_alts_5411_);
v___x_5425_ = lean_box(0);
v___x_5426_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_5424_, v___x_5425_, v_a_5413_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5427_);
lean_dec_ref_known(v___x_5426_, 1);
v_seq_5417_ = v_a_5427_;
goto v___jp_5416_;
}
else
{
lean_dec(v_cases_5410_);
return v___x_5426_;
}
}
else
{
lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5428_ = lean_unsigned_to_nat(0u);
v___x_5429_ = lean_array_fget(v_alts_5411_, v___x_5428_);
lean_dec_ref(v_alts_5411_);
v_seq_5417_ = v___x_5429_;
goto v___jp_5416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_5451_, lean_object* v_alts_5452_, lean_object* v_compress_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_){
_start:
{
uint8_t v_compress_boxed_5457_; lean_object* v_res_5458_; 
v_compress_boxed_5457_ = lean_unbox(v_compress_5453_);
v_res_5458_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_5451_, v_alts_5452_, v_compress_boxed_5457_, v_a_5454_, v_a_5455_);
lean_dec(v_a_5455_);
lean_dec_ref(v_a_5454_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_5459_, lean_object* v_x_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5459_, v_x_5460_, v___y_5461_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_5465_, lean_object* v_x_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_5465_, v_x_5466_, v___y_5467_, v___y_5468_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
return v_res_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v___x_5474_; lean_object* v_env_5475_; uint8_t v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5474_ = lean_st_ref_get(v___y_5472_);
v_env_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc_ref(v_env_5475_);
lean_dec(v___x_5474_);
v___x_5476_ = l_Lean_Meta_isMatcherAppCore(v_env_5475_, v_e_5471_);
v___x_5477_ = lean_box(v___x_5476_);
v___x_5478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5478_, 0, v___x_5477_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5479_, v___y_5480_);
lean_dec(v___y_5480_);
lean_dec_ref(v_e_5479_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v___x_5495_; 
v___x_5495_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5483_, v___y_5493_);
return v___x_5495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_){
_start:
{
lean_object* v_res_5508_; 
v_res_5508_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
lean_dec(v___y_5502_);
lean_dec_ref(v___y_5501_);
lean_dec(v___y_5500_);
lean_dec_ref(v___y_5499_);
lean_dec(v___y_5498_);
lean_dec(v___y_5497_);
lean_dec_ref(v_e_5496_);
return v_res_5508_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5511_ = l_Lean_stringToMessageData(v___x_5510_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5512_, lean_object* v_c_5513_, lean_object* v_a_5514_, lean_object* v_numCases_5515_, uint8_t v_isRec_5516_, lean_object* v_anchorInfo_x3f_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_){
_start:
{
lean_object* v_mvarIds_5530_; lean_object* v___x_5580_; 
v___x_5580_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5512_, v___y_5518_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v_a_5581_; lean_object* v___y_5583_; lean_object* v___x_5635_; uint8_t v___x_5638_; 
v_a_5581_ = lean_ctor_get(v___x_5580_, 0);
lean_inc(v_a_5581_);
lean_dec_ref_known(v___x_5580_, 1);
v___x_5635_ = lean_unsigned_to_nat(1u);
v___x_5638_ = lean_nat_dec_lt(v___x_5635_, v_numCases_5515_);
if (v___x_5638_ == 0)
{
if (v_isRec_5516_ == 0)
{
lean_inc(v_a_5581_);
v___y_5583_ = v_a_5581_;
goto v___jp_5582_;
}
else
{
goto v___jp_5636_;
}
}
else
{
goto v___jp_5636_;
}
v___jp_5582_:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5584_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5513_);
lean_inc_ref(v___x_5512_);
v___x_5585_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5512_, v___y_5583_, v_numCases_5515_, v___x_5584_, v___y_5521_, v___y_5524_, v___y_5526_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v___x_5586_; 
lean_dec_ref_known(v___x_5585_, 1);
lean_inc_ref(v___x_5512_);
v___x_5586_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5512_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v_toCold_5587_; lean_object* v_options_5588_; uint8_t v_hasTrace_5589_; 
lean_dec_ref_known(v___x_5586_, 1);
v_toCold_5587_ = lean_ctor_get(v___y_5526_, 0);
v_options_5588_ = lean_ctor_get(v_toCold_5587_, 2);
v_hasTrace_5589_ = lean_ctor_get_uint8(v_options_5588_, sizeof(void*)*1);
if (v_hasTrace_5589_ == 0)
{
lean_dec(v_a_5581_);
goto v___jp_5533_;
}
else
{
lean_object* v_inheritedTraceOptions_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; uint8_t v___x_5593_; 
v_inheritedTraceOptions_5590_ = lean_ctor_get(v_toCold_5587_, 11);
v___x_5591_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5592_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5590_, v_options_5588_, v___x_5592_);
if (v___x_5593_ == 0)
{
lean_dec(v_a_5581_);
goto v___jp_5533_;
}
else
{
lean_object* v___x_5594_; 
v___x_5594_ = l_Lean_Meta_Grind_updateLastTag(v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
lean_dec_ref_known(v___x_5594_, 1);
lean_inc_ref(v___x_5512_);
v___x_5595_ = l_Lean_MessageData_ofExpr(v___x_5512_);
v___x_5596_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5597_, 0, v___x_5595_);
lean_ctor_set(v___x_5597_, 1, v___x_5596_);
v___x_5598_ = l_Nat_reprFast(v_a_5581_);
v___x_5599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
v___x_5600_ = l_Lean_MessageData_ofFormat(v___x_5599_);
v___x_5601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5601_, 0, v___x_5597_);
lean_ctor_set(v___x_5601_, 1, v___x_5600_);
v___x_5602_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5591_, v___x_5601_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_dec_ref_known(v___x_5602_, 1);
goto v___jp_5533_;
}
else
{
lean_object* v_a_5603_; lean_object* v___x_5605_; uint8_t v_isShared_5606_; uint8_t v_isSharedCheck_5610_; 
lean_dec(v_anchorInfo_x3f_5517_);
lean_dec(v_a_5514_);
lean_dec_ref(v_c_5513_);
lean_dec_ref(v___x_5512_);
v_a_5603_ = lean_ctor_get(v___x_5602_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v___x_5602_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5605_ = v___x_5602_;
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
else
{
lean_inc(v_a_5603_);
lean_dec(v___x_5602_);
v___x_5605_ = lean_box(0);
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
v_resetjp_5604_:
{
lean_object* v___x_5608_; 
if (v_isShared_5606_ == 0)
{
v___x_5608_ = v___x_5605_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
}
else
{
lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5618_; 
lean_dec(v_a_5581_);
lean_dec(v_anchorInfo_x3f_5517_);
lean_dec(v_a_5514_);
lean_dec_ref(v_c_5513_);
lean_dec_ref(v___x_5512_);
v_a_5611_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5618_ == 0)
{
v___x_5613_ = v___x_5594_;
v_isShared_5614_ = v_isSharedCheck_5618_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_dec(v___x_5594_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5618_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5616_; 
if (v_isShared_5614_ == 0)
{
v___x_5616_ = v___x_5613_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
}
}
}
}
else
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5626_; 
lean_dec(v_a_5581_);
lean_dec(v_anchorInfo_x3f_5517_);
lean_dec(v_a_5514_);
lean_dec_ref(v_c_5513_);
lean_dec_ref(v___x_5512_);
v_a_5619_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5621_ = v___x_5586_;
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5586_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
if (v_isShared_5622_ == 0)
{
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5619_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
else
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5634_; 
lean_dec(v_a_5581_);
lean_dec(v_anchorInfo_x3f_5517_);
lean_dec(v_a_5514_);
lean_dec_ref(v_c_5513_);
lean_dec_ref(v___x_5512_);
v_a_5627_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5629_ = v___x_5585_;
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5585_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5632_; 
if (v_isShared_5630_ == 0)
{
v___x_5632_ = v___x_5629_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
v___jp_5636_:
{
lean_object* v___x_5637_; 
v___x_5637_ = lean_nat_add(v_a_5581_, v___x_5635_);
v___y_5583_ = v___x_5637_;
goto v___jp_5582_;
}
}
else
{
lean_object* v_a_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5646_; 
lean_dec(v_anchorInfo_x3f_5517_);
lean_dec(v_numCases_5515_);
lean_dec(v_a_5514_);
lean_dec_ref(v_c_5513_);
lean_dec_ref(v___x_5512_);
v_a_5639_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5646_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5646_ == 0)
{
v___x_5641_ = v___x_5580_;
v_isShared_5642_ = v_isSharedCheck_5646_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_a_5639_);
lean_dec(v___x_5580_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5646_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v___x_5644_; 
if (v_isShared_5642_ == 0)
{
v___x_5644_ = v___x_5641_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
v___x_5644_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
return v___x_5644_;
}
}
}
v___jp_5529_:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5531_, 0, v_mvarIds_5530_);
lean_ctor_set(v___x_5531_, 1, v_anchorInfo_x3f_5517_);
v___x_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5531_);
return v___x_5532_;
}
v___jp_5533_:
{
lean_object* v___x_5534_; 
v___x_5534_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5512_, v___y_5527_);
if (lean_obj_tag(v_c_5513_) == 1)
{
lean_object* v_e_5535_; lean_object* v_binderType_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; 
lean_dec_ref(v___x_5534_);
lean_dec_ref(v___x_5512_);
v_e_5535_ = lean_ctor_get(v_c_5513_, 0);
lean_inc_ref(v_e_5535_);
lean_dec_ref_known(v_c_5513_, 2);
v_binderType_5536_ = lean_ctor_get(v_e_5535_, 1);
lean_inc_ref(v_binderType_5536_);
lean_dec_ref(v_e_5535_);
v___x_5537_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5536_);
v___x_5538_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5514_, v___x_5537_, v___y_5520_, v___y_5521_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_object* v_a_5539_; 
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc(v_a_5539_);
lean_dec_ref_known(v___x_5538_, 1);
v_mvarIds_5530_ = v_a_5539_;
goto v___jp_5529_;
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec(v_anchorInfo_x3f_5517_);
v_a_5540_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5538_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5538_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
else
{
lean_object* v_a_5548_; uint8_t v___x_5549_; 
lean_dec_ref(v_c_5513_);
v_a_5548_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_a_5548_);
lean_dec_ref(v___x_5534_);
v___x_5549_ = lean_unbox(v_a_5548_);
lean_dec(v_a_5548_);
if (v___x_5549_ == 0)
{
lean_object* v___x_5550_; 
v___x_5550_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5512_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5550_) == 0)
{
lean_object* v_a_5551_; lean_object* v___x_5552_; 
v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
lean_inc(v_a_5551_);
lean_dec_ref_known(v___x_5550_, 1);
v___x_5552_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5514_, v_a_5551_, v___y_5520_, v___y_5521_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5552_) == 0)
{
lean_object* v_a_5553_; 
v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
lean_inc(v_a_5553_);
lean_dec_ref_known(v___x_5552_, 1);
v_mvarIds_5530_ = v_a_5553_;
goto v___jp_5529_;
}
else
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5561_; 
lean_dec(v_anchorInfo_x3f_5517_);
v_a_5554_ = lean_ctor_get(v___x_5552_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5556_ = v___x_5552_;
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5552_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5559_; 
if (v_isShared_5557_ == 0)
{
v___x_5559_ = v___x_5556_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
lean_dec(v_anchorInfo_x3f_5517_);
lean_dec(v_a_5514_);
v_a_5562_ = lean_ctor_get(v___x_5550_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5550_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5564_ = v___x_5550_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5550_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
else
{
lean_object* v___x_5570_; 
v___x_5570_ = l_Lean_Meta_Grind_casesMatch(v_a_5514_, v___x_5512_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_a_5571_);
lean_dec_ref_known(v___x_5570_, 1);
v_mvarIds_5530_ = v_a_5571_;
goto v___jp_5529_;
}
else
{
lean_object* v_a_5572_; lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5579_; 
lean_dec(v_anchorInfo_x3f_5517_);
v_a_5572_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5574_ = v___x_5570_;
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
else
{
lean_inc(v_a_5572_);
lean_dec(v___x_5570_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v___x_5577_; 
if (v_isShared_5575_ == 0)
{
v___x_5577_ = v___x_5574_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5572_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5647_ = _args[0];
lean_object* v_c_5648_ = _args[1];
lean_object* v_a_5649_ = _args[2];
lean_object* v_numCases_5650_ = _args[3];
lean_object* v_isRec_5651_ = _args[4];
lean_object* v_anchorInfo_x3f_5652_ = _args[5];
lean_object* v___y_5653_ = _args[6];
lean_object* v___y_5654_ = _args[7];
lean_object* v___y_5655_ = _args[8];
lean_object* v___y_5656_ = _args[9];
lean_object* v___y_5657_ = _args[10];
lean_object* v___y_5658_ = _args[11];
lean_object* v___y_5659_ = _args[12];
lean_object* v___y_5660_ = _args[13];
lean_object* v___y_5661_ = _args[14];
lean_object* v___y_5662_ = _args[15];
lean_object* v___y_5663_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5664_; lean_object* v_res_5665_; 
v_isRec_boxed_5664_ = lean_unbox(v_isRec_5651_);
v_res_5665_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5647_, v_c_5648_, v_a_5649_, v_numCases_5650_, v_isRec_boxed_5664_, v_anchorInfo_x3f_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec(v___y_5653_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5666_, uint8_t v_trace_5667_, lean_object* v___f_5668_, lean_object* v_c_5669_, lean_object* v_candidates_x3f_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
lean_object* v___x_5681_; lean_object* v___y_5683_; 
v___x_5681_ = lean_st_mk_ref(v_goal_5666_);
if (v_trace_5667_ == 0)
{
lean_object* v___x_5702_; lean_object* v___x_5703_; 
lean_dec(v_candidates_x3f_5670_);
v___x_5702_ = lean_box(0);
lean_inc(v___x_5681_);
v___x_5703_ = lean_apply_12(v___f_5668_, v___x_5702_, v___x_5681_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, lean_box(0));
v___y_5683_ = v___x_5703_;
goto v___jp_5682_;
}
else
{
lean_object* v___x_5704_; 
v___x_5704_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5669_, v_candidates_x3f_5670_, v___x_5681_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
if (lean_obj_tag(v___x_5704_) == 0)
{
lean_object* v_a_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
lean_inc(v_a_5705_);
lean_dec_ref_known(v___x_5704_, 1);
v___x_5706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5706_, 0, v_a_5705_);
lean_inc(v___x_5681_);
v___x_5707_ = lean_apply_12(v___f_5668_, v___x_5706_, v___x_5681_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, lean_box(0));
v___y_5683_ = v___x_5707_;
goto v___jp_5682_;
}
else
{
lean_object* v_a_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5715_; 
lean_dec(v___x_5681_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
lean_dec(v___y_5671_);
lean_dec_ref(v___f_5668_);
v_a_5708_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5715_ == 0)
{
v___x_5710_ = v___x_5704_;
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_a_5708_);
lean_dec(v___x_5704_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v___x_5713_; 
if (v_isShared_5711_ == 0)
{
v___x_5713_ = v___x_5710_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_a_5708_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
}
}
v___jp_5682_:
{
if (lean_obj_tag(v___y_5683_) == 0)
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5693_; 
v_a_5684_ = lean_ctor_get(v___y_5683_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___y_5683_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5686_ = v___y_5683_;
v_isShared_5687_ = v_isSharedCheck_5693_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___y_5683_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5693_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5691_; 
v___x_5688_ = lean_st_ref_get(v___x_5681_);
lean_dec(v___x_5681_);
v___x_5689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5689_, 0, v_a_5684_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 0, v___x_5689_);
v___x_5691_ = v___x_5686_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5689_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
else
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
lean_dec(v___x_5681_);
v_a_5694_ = lean_ctor_get(v___y_5683_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___y_5683_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___y_5683_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___y_5683_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5716_, lean_object* v_trace_5717_, lean_object* v___f_5718_, lean_object* v_c_5719_, lean_object* v_candidates_x3f_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
uint8_t v_trace_boxed_5731_; lean_object* v_res_5732_; 
v_trace_boxed_5731_ = lean_unbox(v_trace_5717_);
v_res_5732_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5716_, v_trace_boxed_5731_, v___f_5718_, v_c_5719_, v_candidates_x3f_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
lean_dec_ref(v_c_5719_);
return v_res_5732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object* v_snd_5733_, lean_object* v_a_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
lean_object* v___x_5745_; 
v___x_5745_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5733_, v___y_5737_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5747_; 
v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
lean_inc(v_a_5746_);
lean_dec_ref_known(v___x_5745_, 1);
lean_inc(v_a_5734_);
v___x_5747_ = l_Lean_MVarId_getType(v_a_5734_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v_a_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
lean_inc(v_a_5748_);
lean_dec_ref_known(v___x_5747_, 1);
v___x_5749_ = l_Lean_mkMVar(v_a_5734_);
v___x_5750_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5746_, v___x_5749_, v_a_5748_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
return v___x_5750_;
}
else
{
lean_dec(v_a_5746_);
lean_dec(v_a_5734_);
return v___x_5747_;
}
}
else
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
lean_dec(v_a_5734_);
v_a_5751_ = lean_ctor_get(v___x_5745_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5745_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5753_ = v___x_5745_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5745_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object* v_snd_5759_, lean_object* v_a_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(v_snd_5759_, v_a_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v_snd_5759_);
return v_res_5771_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; 
v___x_5774_ = lean_box(0);
v___x_5775_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0));
v___x_5776_ = l_Lean_mkConst(v___x_5775_, v___x_5774_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(lean_object* v___x_5777_, lean_object* v_snd_5778_, lean_object* v___x_5779_, lean_object* v_i_5780_, lean_object* v_falseProof_5781_, lean_object* v_seq_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_){
_start:
{
lean_object* v___x_5793_; lean_object* v_congrThms_5794_; lean_object* v_simp_5795_; lean_object* v_symSimp_5796_; lean_object* v_symDSimp_5797_; lean_object* v_lastTag_5798_; lean_object* v_counters_5799_; lean_object* v_splitDiags_5800_; lean_object* v_ematchDiags_5801_; lean_object* v_lawfulEqCmpMap_5802_; lean_object* v_reflCmpMap_5803_; lean_object* v_anchors_5804_; lean_object* v_fvarAnchors_5805_; lean_object* v_instanceMap_5806_; lean_object* v_hoistedDecls_5807_; lean_object* v_proofInfos_5808_; lean_object* v_numBranches_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5862_; 
v___x_5793_ = lean_st_ref_take(v___y_5785_);
v_congrThms_5794_ = lean_ctor_get(v___x_5793_, 0);
v_simp_5795_ = lean_ctor_get(v___x_5793_, 1);
v_symSimp_5796_ = lean_ctor_get(v___x_5793_, 2);
v_symDSimp_5797_ = lean_ctor_get(v___x_5793_, 3);
v_lastTag_5798_ = lean_ctor_get(v___x_5793_, 4);
v_counters_5799_ = lean_ctor_get(v___x_5793_, 5);
v_splitDiags_5800_ = lean_ctor_get(v___x_5793_, 6);
v_ematchDiags_5801_ = lean_ctor_get(v___x_5793_, 7);
v_lawfulEqCmpMap_5802_ = lean_ctor_get(v___x_5793_, 8);
v_reflCmpMap_5803_ = lean_ctor_get(v___x_5793_, 9);
v_anchors_5804_ = lean_ctor_get(v___x_5793_, 10);
v_fvarAnchors_5805_ = lean_ctor_get(v___x_5793_, 11);
v_instanceMap_5806_ = lean_ctor_get(v___x_5793_, 12);
v_hoistedDecls_5807_ = lean_ctor_get(v___x_5793_, 13);
v_proofInfos_5808_ = lean_ctor_get(v___x_5793_, 14);
v_numBranches_5809_ = lean_ctor_get(v___x_5793_, 15);
v_isSharedCheck_5862_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5862_ == 0)
{
v___x_5811_ = v___x_5793_;
v_isShared_5812_ = v_isSharedCheck_5862_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_numBranches_5809_);
lean_inc(v_proofInfos_5808_);
lean_inc(v_hoistedDecls_5807_);
lean_inc(v_instanceMap_5806_);
lean_inc(v_fvarAnchors_5805_);
lean_inc(v_anchors_5804_);
lean_inc(v_reflCmpMap_5803_);
lean_inc(v_lawfulEqCmpMap_5802_);
lean_inc(v_ematchDiags_5801_);
lean_inc(v_splitDiags_5800_);
lean_inc(v_counters_5799_);
lean_inc(v_lastTag_5798_);
lean_inc(v_symDSimp_5797_);
lean_inc(v_symSimp_5796_);
lean_inc(v_simp_5795_);
lean_inc(v_congrThms_5794_);
lean_dec(v___x_5793_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5862_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5818_; 
v___x_5813_ = lean_unsigned_to_nat(1u);
v___x_5814_ = lean_nat_sub(v___x_5777_, v___x_5813_);
v___x_5815_ = lean_nat_sub(v___x_5814_, v_i_5780_);
lean_dec(v___x_5814_);
v___x_5816_ = lean_nat_sub(v_numBranches_5809_, v___x_5815_);
lean_dec(v___x_5815_);
lean_dec(v_numBranches_5809_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 15, v___x_5816_);
v___x_5818_ = v___x_5811_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_congrThms_5794_);
lean_ctor_set(v_reuseFailAlloc_5861_, 1, v_simp_5795_);
lean_ctor_set(v_reuseFailAlloc_5861_, 2, v_symSimp_5796_);
lean_ctor_set(v_reuseFailAlloc_5861_, 3, v_symDSimp_5797_);
lean_ctor_set(v_reuseFailAlloc_5861_, 4, v_lastTag_5798_);
lean_ctor_set(v_reuseFailAlloc_5861_, 5, v_counters_5799_);
lean_ctor_set(v_reuseFailAlloc_5861_, 6, v_splitDiags_5800_);
lean_ctor_set(v_reuseFailAlloc_5861_, 7, v_ematchDiags_5801_);
lean_ctor_set(v_reuseFailAlloc_5861_, 8, v_lawfulEqCmpMap_5802_);
lean_ctor_set(v_reuseFailAlloc_5861_, 9, v_reflCmpMap_5803_);
lean_ctor_set(v_reuseFailAlloc_5861_, 10, v_anchors_5804_);
lean_ctor_set(v_reuseFailAlloc_5861_, 11, v_fvarAnchors_5805_);
lean_ctor_set(v_reuseFailAlloc_5861_, 12, v_instanceMap_5806_);
lean_ctor_set(v_reuseFailAlloc_5861_, 13, v_hoistedDecls_5807_);
lean_ctor_set(v_reuseFailAlloc_5861_, 14, v_proofInfos_5808_);
lean_ctor_set(v_reuseFailAlloc_5861_, 15, v___x_5816_);
v___x_5818_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5819_ = lean_st_ref_put(v___y_5785_, v___x_5818_);
v___x_5820_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5778_, v___y_5785_);
if (lean_obj_tag(v___x_5820_) == 0)
{
lean_object* v_a_5821_; lean_object* v_mvarId_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v_a_5821_ = lean_ctor_get(v___x_5820_, 0);
lean_inc(v_a_5821_);
lean_dec_ref_known(v___x_5820_, 1);
v_mvarId_5822_ = lean_ctor_get(v_snd_5778_, 1);
lean_inc(v_mvarId_5822_);
lean_dec_ref(v_snd_5778_);
v___x_5823_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_5824_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkHoistedDecls___boxed), 13, 3);
lean_closure_set(v___x_5824_, 0, v_a_5821_);
lean_closure_set(v___x_5824_, 1, v_falseProof_5781_);
lean_closure_set(v___x_5824_, 2, v___x_5823_);
v___x_5825_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5822_, v___x_5824_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_);
if (lean_obj_tag(v___x_5825_) == 0)
{
lean_object* v_a_5826_; lean_object* v___x_5827_; 
v_a_5826_ = lean_ctor_get(v___x_5825_, 0);
lean_inc(v_a_5826_);
lean_dec_ref_known(v___x_5825_, 1);
v___x_5827_ = l_Lean_MVarId_assignFalseProof(v___x_5779_, v_a_5826_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_);
if (lean_obj_tag(v___x_5827_) == 0)
{
lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5835_; 
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5835_ == 0)
{
lean_object* v_unused_5836_; 
v_unused_5836_ = lean_ctor_get(v___x_5827_, 0);
lean_dec(v_unused_5836_);
v___x_5829_ = v___x_5827_;
v_isShared_5830_ = v_isSharedCheck_5835_;
goto v_resetjp_5828_;
}
else
{
lean_dec(v___x_5827_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5835_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
lean_object* v___x_5831_; lean_object* v___x_5833_; 
v___x_5831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5831_, 0, v_seq_5782_);
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 0, v___x_5831_);
v___x_5833_ = v___x_5829_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v___x_5831_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
else
{
lean_object* v_a_5837_; lean_object* v___x_5839_; uint8_t v_isShared_5840_; uint8_t v_isSharedCheck_5844_; 
lean_dec(v_seq_5782_);
v_a_5837_ = lean_ctor_get(v___x_5827_, 0);
v_isSharedCheck_5844_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5844_ == 0)
{
v___x_5839_ = v___x_5827_;
v_isShared_5840_ = v_isSharedCheck_5844_;
goto v_resetjp_5838_;
}
else
{
lean_inc(v_a_5837_);
lean_dec(v___x_5827_);
v___x_5839_ = lean_box(0);
v_isShared_5840_ = v_isSharedCheck_5844_;
goto v_resetjp_5838_;
}
v_resetjp_5838_:
{
lean_object* v___x_5842_; 
if (v_isShared_5840_ == 0)
{
v___x_5842_ = v___x_5839_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_a_5837_);
v___x_5842_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
return v___x_5842_;
}
}
}
}
else
{
lean_object* v_a_5845_; lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5852_; 
lean_dec(v_seq_5782_);
lean_dec(v___x_5779_);
v_a_5845_ = lean_ctor_get(v___x_5825_, 0);
v_isSharedCheck_5852_ = !lean_is_exclusive(v___x_5825_);
if (v_isSharedCheck_5852_ == 0)
{
v___x_5847_ = v___x_5825_;
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
else
{
lean_inc(v_a_5845_);
lean_dec(v___x_5825_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v___x_5850_; 
if (v_isShared_5848_ == 0)
{
v___x_5850_ = v___x_5847_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
}
else
{
lean_object* v_a_5853_; lean_object* v___x_5855_; uint8_t v_isShared_5856_; uint8_t v_isSharedCheck_5860_; 
lean_dec(v_seq_5782_);
lean_dec_ref(v_falseProof_5781_);
lean_dec(v___x_5779_);
lean_dec_ref(v_snd_5778_);
v_a_5853_ = lean_ctor_get(v___x_5820_, 0);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5820_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5855_ = v___x_5820_;
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
else
{
lean_inc(v_a_5853_);
lean_dec(v___x_5820_);
v___x_5855_ = lean_box(0);
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
v_resetjp_5854_:
{
lean_object* v___x_5858_; 
if (v_isShared_5856_ == 0)
{
v___x_5858_ = v___x_5855_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___boxed(lean_object* v___x_5863_, lean_object* v_snd_5864_, lean_object* v___x_5865_, lean_object* v_i_5866_, lean_object* v_falseProof_5867_, lean_object* v_seq_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_){
_start:
{
lean_object* v_res_5879_; 
v_res_5879_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5863_, v_snd_5864_, v___x_5865_, v_i_5866_, v_falseProof_5867_, v_seq_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_);
lean_dec(v___y_5877_);
lean_dec_ref(v___y_5876_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
lean_dec(v___y_5871_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5869_);
lean_dec(v_i_5866_);
lean_dec(v___x_5863_);
return v_res_5879_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v___x_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_){
_start:
{
if (lean_obj_tag(v_a_5881_) == 0)
{
lean_object* v___x_5883_; 
v___x_5883_ = l_List_reverse___redArg(v_a_5882_);
return v___x_5883_;
}
else
{
lean_object* v_head_5884_; lean_object* v_toGoalState_5885_; lean_object* v_tail_5886_; lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5935_; 
v_head_5884_ = lean_ctor_get(v_a_5881_, 0);
lean_inc(v_head_5884_);
v_toGoalState_5885_ = lean_ctor_get(v_head_5884_, 0);
lean_inc_ref(v_toGoalState_5885_);
v_tail_5886_ = lean_ctor_get(v_a_5881_, 1);
v_isSharedCheck_5935_ = !lean_is_exclusive(v_a_5881_);
if (v_isSharedCheck_5935_ == 0)
{
lean_object* v_unused_5936_; 
v_unused_5936_ = lean_ctor_get(v_a_5881_, 0);
lean_dec(v_unused_5936_);
v___x_5888_ = v_a_5881_;
v_isShared_5889_ = v_isSharedCheck_5935_;
goto v_resetjp_5887_;
}
else
{
lean_inc(v_tail_5886_);
lean_dec(v_a_5881_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5935_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v_mvarId_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5933_; 
v_mvarId_5890_ = lean_ctor_get(v_head_5884_, 1);
v_isSharedCheck_5933_ = !lean_is_exclusive(v_head_5884_);
if (v_isSharedCheck_5933_ == 0)
{
lean_object* v_unused_5934_; 
v_unused_5934_ = lean_ctor_get(v_head_5884_, 0);
lean_dec(v_unused_5934_);
v___x_5892_ = v_head_5884_;
v_isShared_5893_ = v_isSharedCheck_5933_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_mvarId_5890_);
lean_dec(v_head_5884_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5933_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v_nextDeclIdx_5894_; lean_object* v_enodeMap_5895_; lean_object* v_exprs_5896_; lean_object* v_parents_5897_; lean_object* v_congrTable_5898_; lean_object* v_appMap_5899_; lean_object* v_indicesFound_5900_; lean_object* v_toProcess_5901_; lean_object* v_internalizing_5902_; uint8_t v_inconsistent_5903_; lean_object* v_nextIdx_5904_; lean_object* v_newRawFacts_5905_; lean_object* v_facts_5906_; lean_object* v_extThms_5907_; lean_object* v_ematch_5908_; lean_object* v_inj_5909_; lean_object* v_split_5910_; lean_object* v_clean_5911_; lean_object* v_sstates_5912_; lean_object* v_goalStack_5913_; uint64_t v_introBase_5914_; lean_object* v_numIntros_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5932_; 
v_nextDeclIdx_5894_ = lean_ctor_get(v_toGoalState_5885_, 0);
v_enodeMap_5895_ = lean_ctor_get(v_toGoalState_5885_, 1);
v_exprs_5896_ = lean_ctor_get(v_toGoalState_5885_, 2);
v_parents_5897_ = lean_ctor_get(v_toGoalState_5885_, 3);
v_congrTable_5898_ = lean_ctor_get(v_toGoalState_5885_, 4);
v_appMap_5899_ = lean_ctor_get(v_toGoalState_5885_, 5);
v_indicesFound_5900_ = lean_ctor_get(v_toGoalState_5885_, 6);
v_toProcess_5901_ = lean_ctor_get(v_toGoalState_5885_, 7);
v_internalizing_5902_ = lean_ctor_get(v_toGoalState_5885_, 8);
v_inconsistent_5903_ = lean_ctor_get_uint8(v_toGoalState_5885_, sizeof(void*)*20 + 8);
v_nextIdx_5904_ = lean_ctor_get(v_toGoalState_5885_, 9);
v_newRawFacts_5905_ = lean_ctor_get(v_toGoalState_5885_, 10);
v_facts_5906_ = lean_ctor_get(v_toGoalState_5885_, 11);
v_extThms_5907_ = lean_ctor_get(v_toGoalState_5885_, 12);
v_ematch_5908_ = lean_ctor_get(v_toGoalState_5885_, 13);
v_inj_5909_ = lean_ctor_get(v_toGoalState_5885_, 14);
v_split_5910_ = lean_ctor_get(v_toGoalState_5885_, 15);
v_clean_5911_ = lean_ctor_get(v_toGoalState_5885_, 16);
v_sstates_5912_ = lean_ctor_get(v_toGoalState_5885_, 17);
v_goalStack_5913_ = lean_ctor_get(v_toGoalState_5885_, 18);
v_introBase_5914_ = lean_ctor_get_uint64(v_toGoalState_5885_, sizeof(void*)*20);
v_numIntros_5915_ = lean_ctor_get(v_toGoalState_5885_, 19);
v_isSharedCheck_5932_ = !lean_is_exclusive(v_toGoalState_5885_);
if (v_isSharedCheck_5932_ == 0)
{
v___x_5917_ = v_toGoalState_5885_;
v_isShared_5918_ = v_isSharedCheck_5932_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_numIntros_5915_);
lean_inc(v_goalStack_5913_);
lean_inc(v_sstates_5912_);
lean_inc(v_clean_5911_);
lean_inc(v_split_5910_);
lean_inc(v_inj_5909_);
lean_inc(v_ematch_5908_);
lean_inc(v_extThms_5907_);
lean_inc(v_facts_5906_);
lean_inc(v_newRawFacts_5905_);
lean_inc(v_nextIdx_5904_);
lean_inc(v_internalizing_5902_);
lean_inc(v_toProcess_5901_);
lean_inc(v_indicesFound_5900_);
lean_inc(v_appMap_5899_);
lean_inc(v_congrTable_5898_);
lean_inc(v_parents_5897_);
lean_inc(v_exprs_5896_);
lean_inc(v_enodeMap_5895_);
lean_inc(v_nextDeclIdx_5894_);
lean_dec(v_toGoalState_5885_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5932_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5923_; 
v___x_5919_ = lean_unsigned_to_nat(0u);
v___x_5920_ = lean_array_get_size(v___x_5880_);
v___x_5921_ = l_Array_extract___redArg(v_goalStack_5913_, v___x_5919_, v___x_5920_);
lean_dec_ref(v_goalStack_5913_);
if (v_isShared_5918_ == 0)
{
lean_ctor_set(v___x_5917_, 18, v___x_5921_);
v___x_5923_ = v___x_5917_;
goto v_reusejp_5922_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_nextDeclIdx_5894_);
lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_enodeMap_5895_);
lean_ctor_set(v_reuseFailAlloc_5931_, 2, v_exprs_5896_);
lean_ctor_set(v_reuseFailAlloc_5931_, 3, v_parents_5897_);
lean_ctor_set(v_reuseFailAlloc_5931_, 4, v_congrTable_5898_);
lean_ctor_set(v_reuseFailAlloc_5931_, 5, v_appMap_5899_);
lean_ctor_set(v_reuseFailAlloc_5931_, 6, v_indicesFound_5900_);
lean_ctor_set(v_reuseFailAlloc_5931_, 7, v_toProcess_5901_);
lean_ctor_set(v_reuseFailAlloc_5931_, 8, v_internalizing_5902_);
lean_ctor_set(v_reuseFailAlloc_5931_, 9, v_nextIdx_5904_);
lean_ctor_set(v_reuseFailAlloc_5931_, 10, v_newRawFacts_5905_);
lean_ctor_set(v_reuseFailAlloc_5931_, 11, v_facts_5906_);
lean_ctor_set(v_reuseFailAlloc_5931_, 12, v_extThms_5907_);
lean_ctor_set(v_reuseFailAlloc_5931_, 13, v_ematch_5908_);
lean_ctor_set(v_reuseFailAlloc_5931_, 14, v_inj_5909_);
lean_ctor_set(v_reuseFailAlloc_5931_, 15, v_split_5910_);
lean_ctor_set(v_reuseFailAlloc_5931_, 16, v_clean_5911_);
lean_ctor_set(v_reuseFailAlloc_5931_, 17, v_sstates_5912_);
lean_ctor_set(v_reuseFailAlloc_5931_, 18, v___x_5921_);
lean_ctor_set(v_reuseFailAlloc_5931_, 19, v_numIntros_5915_);
lean_ctor_set_uint8(v_reuseFailAlloc_5931_, sizeof(void*)*20 + 8, v_inconsistent_5903_);
lean_ctor_set_uint64(v_reuseFailAlloc_5931_, sizeof(void*)*20, v_introBase_5914_);
v___x_5923_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5922_;
}
v_reusejp_5922_:
{
lean_object* v___x_5925_; 
if (v_isShared_5893_ == 0)
{
lean_ctor_set(v___x_5892_, 0, v___x_5923_);
v___x_5925_ = v___x_5892_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5930_, 1, v_mvarId_5890_);
v___x_5925_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
lean_object* v___x_5927_; 
if (v_isShared_5889_ == 0)
{
lean_ctor_set(v___x_5888_, 1, v_a_5882_);
lean_ctor_set(v___x_5888_, 0, v___x_5925_);
v___x_5927_ = v___x_5888_;
goto v_reusejp_5926_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5929_, 1, v_a_5882_);
v___x_5927_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5926_;
}
v_reusejp_5926_:
{
v_a_5881_ = v_tail_5886_;
v_a_5882_ = v___x_5927_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v___x_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_){
_start:
{
lean_object* v_res_5940_; 
v_res_5940_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5937_, v_a_5938_, v_a_5939_);
lean_dec_ref(v___x_5937_);
return v_res_5940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(lean_object* v___x_5941_, lean_object* v_gs_5942_){
_start:
{
lean_object* v___x_5943_; lean_object* v___x_5944_; 
v___x_5943_ = lean_box(0);
v___x_5944_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5941_, v_gs_5942_, v___x_5943_);
return v___x_5944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0___boxed(lean_object* v___x_5945_, lean_object* v_gs_5946_){
_start:
{
lean_object* v_res_5947_; 
v_res_5947_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5945_, v_gs_5946_);
lean_dec_ref(v___x_5945_);
return v_res_5947_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5948_, lean_object* v_a_5949_, lean_object* v_goal_5950_, lean_object* v___x_5951_, lean_object* v_snd_5952_, lean_object* v___x_5953_, uint8_t v_stopAtFirstFailure_5954_, lean_object* v___x_5955_, lean_object* v_as_x27_5956_, lean_object* v_b_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_){
_start:
{
if (lean_obj_tag(v_as_x27_5956_) == 0)
{
lean_object* v___x_5968_; 
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v___x_5968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5968_, 0, v_b_5957_);
return v___x_5968_;
}
else
{
lean_object* v_snd_5969_; lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_6250_; 
v_snd_5969_ = lean_ctor_get(v_b_5957_, 1);
v_isSharedCheck_6250_ = !lean_is_exclusive(v_b_5957_);
if (v_isSharedCheck_6250_ == 0)
{
lean_object* v_unused_6251_; 
v_unused_6251_ = lean_ctor_get(v_b_5957_, 0);
lean_dec(v_unused_6251_);
v___x_5971_ = v_b_5957_;
v_isShared_5972_ = v_isSharedCheck_6250_;
goto v_resetjp_5970_;
}
else
{
lean_inc(v_snd_5969_);
lean_dec(v_b_5957_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_6250_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v_snd_5973_; lean_object* v_snd_5974_; lean_object* v_snd_5975_; lean_object* v_head_5976_; lean_object* v_tail_5977_; lean_object* v_fst_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_6248_; 
v_snd_5973_ = lean_ctor_get(v_snd_5969_, 1);
lean_inc(v_snd_5973_);
v_snd_5974_ = lean_ctor_get(v_snd_5973_, 1);
lean_inc(v_snd_5974_);
v_snd_5975_ = lean_ctor_get(v_snd_5974_, 1);
lean_inc(v_snd_5975_);
v_head_5976_ = lean_ctor_get(v_as_x27_5956_, 0);
v_tail_5977_ = lean_ctor_get(v_as_x27_5956_, 1);
v_fst_5978_ = lean_ctor_get(v_snd_5969_, 0);
v_isSharedCheck_6248_ = !lean_is_exclusive(v_snd_5969_);
if (v_isSharedCheck_6248_ == 0)
{
lean_object* v_unused_6249_; 
v_unused_6249_ = lean_ctor_get(v_snd_5969_, 1);
lean_dec(v_unused_6249_);
v___x_5980_ = v_snd_5969_;
v_isShared_5981_ = v_isSharedCheck_6248_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_fst_5978_);
lean_dec(v_snd_5969_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_6248_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
lean_object* v_fst_5982_; lean_object* v___x_5984_; uint8_t v_isShared_5985_; uint8_t v_isSharedCheck_6246_; 
v_fst_5982_ = lean_ctor_get(v_snd_5973_, 0);
v_isSharedCheck_6246_ = !lean_is_exclusive(v_snd_5973_);
if (v_isSharedCheck_6246_ == 0)
{
lean_object* v_unused_6247_; 
v_unused_6247_ = lean_ctor_get(v_snd_5973_, 1);
lean_dec(v_unused_6247_);
v___x_5984_ = v_snd_5973_;
v_isShared_5985_ = v_isSharedCheck_6246_;
goto v_resetjp_5983_;
}
else
{
lean_inc(v_fst_5982_);
lean_dec(v_snd_5973_);
v___x_5984_ = lean_box(0);
v_isShared_5985_ = v_isSharedCheck_6246_;
goto v_resetjp_5983_;
}
v_resetjp_5983_:
{
lean_object* v_fst_5986_; lean_object* v___x_5988_; uint8_t v_isShared_5989_; uint8_t v_isSharedCheck_6244_; 
v_fst_5986_ = lean_ctor_get(v_snd_5974_, 0);
v_isSharedCheck_6244_ = !lean_is_exclusive(v_snd_5974_);
if (v_isSharedCheck_6244_ == 0)
{
lean_object* v_unused_6245_; 
v_unused_6245_ = lean_ctor_get(v_snd_5974_, 1);
lean_dec(v_unused_6245_);
v___x_5988_ = v_snd_5974_;
v_isShared_5989_ = v_isSharedCheck_6244_;
goto v_resetjp_5987_;
}
else
{
lean_inc(v_fst_5986_);
lean_dec(v_snd_5974_);
v___x_5988_ = lean_box(0);
v_isShared_5989_ = v_isSharedCheck_6244_;
goto v_resetjp_5987_;
}
v_resetjp_5987_:
{
lean_object* v_start_5990_; lean_object* v_stop_5991_; lean_object* v_step_5992_; lean_object* v___x_5993_; uint8_t v___x_5994_; 
v_start_5990_ = lean_ctor_get(v_snd_5975_, 0);
v_stop_5991_ = lean_ctor_get(v_snd_5975_, 1);
v_step_5992_ = lean_ctor_get(v_snd_5975_, 2);
v___x_5993_ = lean_box(0);
v___x_5994_ = lean_nat_dec_lt(v_start_5990_, v_stop_5991_);
if (v___x_5994_ == 0)
{
lean_object* v___x_5996_; 
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
if (v_isShared_5989_ == 0)
{
v___x_5996_ = v___x_5988_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_fst_5986_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v_snd_5975_);
v___x_5996_ = v_reuseFailAlloc_6007_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
lean_object* v___x_5998_; 
if (v_isShared_5985_ == 0)
{
lean_ctor_set(v___x_5984_, 1, v___x_5996_);
v___x_5998_ = v___x_5984_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_fst_5982_);
lean_ctor_set(v_reuseFailAlloc_6006_, 1, v___x_5996_);
v___x_5998_ = v_reuseFailAlloc_6006_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
lean_object* v___x_6000_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v___x_5998_);
v___x_6000_ = v___x_5980_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v_fst_5978_);
lean_ctor_set(v_reuseFailAlloc_6005_, 1, v___x_5998_);
v___x_6000_ = v_reuseFailAlloc_6005_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
lean_object* v___x_6002_; 
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_6000_);
lean_ctor_set(v___x_5971_, 0, v___x_5993_);
v___x_6002_ = v___x_5971_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v___x_5993_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v___x_6000_);
v___x_6002_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
lean_object* v___x_6003_; 
v___x_6003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
return v___x_6003_;
}
}
}
}
}
else
{
lean_object* v___x_6009_; uint8_t v_isShared_6010_; uint8_t v_isSharedCheck_6240_; 
lean_inc(v_step_5992_);
lean_inc(v_stop_5991_);
lean_inc(v_start_5990_);
v_isSharedCheck_6240_ = !lean_is_exclusive(v_snd_5975_);
if (v_isSharedCheck_6240_ == 0)
{
lean_object* v_unused_6241_; lean_object* v_unused_6242_; lean_object* v_unused_6243_; 
v_unused_6241_ = lean_ctor_get(v_snd_5975_, 2);
lean_dec(v_unused_6241_);
v_unused_6242_ = lean_ctor_get(v_snd_5975_, 1);
lean_dec(v_unused_6242_);
v_unused_6243_ = lean_ctor_get(v_snd_5975_, 0);
lean_dec(v_unused_6243_);
v___x_6009_ = v_snd_5975_;
v_isShared_6010_ = v_isSharedCheck_6240_;
goto v_resetjp_6008_;
}
else
{
lean_dec(v_snd_5975_);
v___x_6009_ = lean_box(0);
v_isShared_6010_ = v_isSharedCheck_6240_;
goto v_resetjp_6008_;
}
v_resetjp_6008_:
{
lean_object* v___x_6011_; lean_object* v___x_6013_; 
v___x_6011_ = lean_nat_add(v_start_5990_, v_step_5992_);
if (v_isShared_6010_ == 0)
{
lean_ctor_set(v___x_6009_, 0, v___x_6011_);
v___x_6013_ = v___x_6009_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6239_; 
v_reuseFailAlloc_6239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6239_, 0, v___x_6011_);
lean_ctor_set(v_reuseFailAlloc_6239_, 1, v_stop_5991_);
lean_ctor_set(v_reuseFailAlloc_6239_, 2, v_step_5992_);
v___x_6013_ = v_reuseFailAlloc_6239_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
lean_object* v___x_6014_; 
lean_inc_ref(v_kp_5948_);
lean_inc(v___y_5966_);
lean_inc_ref(v___y_5965_);
lean_inc(v___y_5964_);
lean_inc_ref(v___y_5963_);
lean_inc(v___y_5962_);
lean_inc_ref(v___y_5961_);
lean_inc(v___y_5960_);
lean_inc_ref(v___y_5959_);
lean_inc(v___y_5958_);
lean_inc(v_head_5976_);
v___x_6014_ = lean_apply_11(v_kp_5948_, v_head_5976_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, lean_box(0));
if (lean_obj_tag(v___x_6014_) == 0)
{
lean_object* v_a_6015_; lean_object* v___x_6017_; uint8_t v_isShared_6018_; uint8_t v_isSharedCheck_6230_; 
v_a_6015_ = lean_ctor_get(v___x_6014_, 0);
v_isSharedCheck_6230_ = !lean_is_exclusive(v___x_6014_);
if (v_isSharedCheck_6230_ == 0)
{
v___x_6017_ = v___x_6014_;
v_isShared_6018_ = v_isSharedCheck_6230_;
goto v_resetjp_6016_;
}
else
{
lean_inc(v_a_6015_);
lean_dec(v___x_6014_);
v___x_6017_ = lean_box(0);
v_isShared_6018_ = v_isSharedCheck_6230_;
goto v_resetjp_6016_;
}
v_resetjp_6016_:
{
if (lean_obj_tag(v_a_6015_) == 0)
{
lean_object* v_seq_6019_; lean_object* v_ncb_x3f_6021_; lean_object* v_mvarId_6050_; lean_object* v___x_6051_; 
lean_del_object(v___x_6017_);
v_seq_6019_ = lean_ctor_get(v_a_6015_, 0);
lean_inc(v_seq_6019_);
lean_dec_ref_known(v_a_6015_, 1);
v_mvarId_6050_ = lean_ctor_get(v_head_5976_, 1);
lean_inc(v_mvarId_6050_);
v___x_6051_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_6050_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
if (lean_obj_tag(v___x_6051_) == 0)
{
lean_object* v_a_6052_; 
v_a_6052_ = lean_ctor_get(v___x_6051_, 0);
lean_inc(v_a_6052_);
lean_dec_ref_known(v___x_6051_, 1);
if (lean_obj_tag(v_a_6052_) == 1)
{
lean_object* v_val_6053_; lean_object* v___x_6055_; uint8_t v_isShared_6056_; uint8_t v_isSharedCheck_6108_; 
v_val_6053_ = lean_ctor_get(v_a_6052_, 0);
v_isSharedCheck_6108_ = !lean_is_exclusive(v_a_6052_);
if (v_isSharedCheck_6108_ == 0)
{
v___x_6055_ = v_a_6052_;
v_isShared_6056_ = v_isSharedCheck_6108_;
goto v_resetjp_6054_;
}
else
{
lean_inc(v_val_6053_);
lean_dec(v_a_6052_);
v___x_6055_ = lean_box(0);
v_isShared_6056_ = v_isSharedCheck_6108_;
goto v_resetjp_6054_;
}
v_resetjp_6054_:
{
lean_object* v___x_6057_; 
lean_inc(v_seq_6019_);
lean_inc_ref(v_goal_5950_);
lean_inc(v_a_5949_);
v___x_6057_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_5949_, v_goal_5950_, v_seq_6019_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
if (lean_obj_tag(v___x_6057_) == 0)
{
lean_object* v_a_6058_; uint8_t v___x_6059_; 
v_a_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_a_6058_);
lean_dec_ref_known(v___x_6057_, 1);
v___x_6059_ = lean_unbox(v_a_6058_);
lean_dec(v_a_6058_);
if (v___x_6059_ == 0)
{
if (lean_obj_tag(v_fst_5986_) == 0)
{
lean_object* v___x_6060_; 
v___x_6060_ = l_Lean_Meta_Grind_saveState___redArg(v___y_5960_, v___y_5964_, v___y_5966_);
if (lean_obj_tag(v___x_6060_) == 0)
{
lean_object* v_a_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6066_; 
v_a_6061_ = lean_ctor_get(v___x_6060_, 0);
lean_inc(v_a_6061_);
lean_dec_ref_known(v___x_6060_, 1);
lean_inc(v_seq_6019_);
v___x_6062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6062_, 0, v_val_6053_);
lean_ctor_set(v___x_6062_, 1, v_seq_6019_);
v___x_6063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6063_, 0, v_start_5990_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___x_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6064_, 0, v_a_6061_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
if (v_isShared_6056_ == 0)
{
lean_ctor_set(v___x_6055_, 0, v___x_6064_);
v___x_6066_ = v___x_6055_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6067_; 
v_reuseFailAlloc_6067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6067_, 0, v___x_6064_);
v___x_6066_ = v_reuseFailAlloc_6067_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
v_ncb_x3f_6021_ = v___x_6066_;
goto v___jp_6020_;
}
}
else
{
lean_object* v_a_6068_; lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6075_; 
lean_del_object(v___x_6055_);
lean_dec(v_val_6053_);
lean_dec(v_seq_6019_);
lean_dec_ref(v___x_6013_);
lean_dec(v_start_5990_);
lean_del_object(v___x_5988_);
lean_del_object(v___x_5984_);
lean_dec(v_fst_5982_);
lean_del_object(v___x_5980_);
lean_dec(v_fst_5978_);
lean_del_object(v___x_5971_);
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v_a_6068_ = lean_ctor_get(v___x_6060_, 0);
v_isSharedCheck_6075_ = !lean_is_exclusive(v___x_6060_);
if (v_isSharedCheck_6075_ == 0)
{
v___x_6070_ = v___x_6060_;
v_isShared_6071_ = v_isSharedCheck_6075_;
goto v_resetjp_6069_;
}
else
{
lean_inc(v_a_6068_);
lean_dec(v___x_6060_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6075_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
lean_object* v___x_6073_; 
if (v_isShared_6071_ == 0)
{
v___x_6073_ = v___x_6070_;
goto v_reusejp_6072_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6068_);
v___x_6073_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6072_;
}
v_reusejp_6072_:
{
return v___x_6073_;
}
}
}
}
else
{
lean_del_object(v___x_6055_);
lean_dec(v_val_6053_);
lean_dec(v_start_5990_);
v_ncb_x3f_6021_ = v_fst_5986_;
goto v___jp_6020_;
}
}
else
{
lean_object* v___x_6076_; 
lean_del_object(v___x_5988_);
lean_del_object(v___x_5984_);
lean_del_object(v___x_5980_);
lean_del_object(v___x_5971_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v___x_6076_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5951_, v_snd_5952_, v___x_5953_, v_start_5990_, v_val_6053_, v_seq_6019_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
lean_dec(v_start_5990_);
if (lean_obj_tag(v___x_6076_) == 0)
{
lean_object* v_a_6077_; lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6091_; 
v_a_6077_ = lean_ctor_get(v___x_6076_, 0);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6076_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6079_ = v___x_6076_;
v_isShared_6080_ = v_isSharedCheck_6091_;
goto v_resetjp_6078_;
}
else
{
lean_inc(v_a_6077_);
lean_dec(v___x_6076_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6091_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v___x_6082_; 
if (v_isShared_6056_ == 0)
{
lean_ctor_set(v___x_6055_, 0, v_a_6077_);
v___x_6082_ = v___x_6055_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_a_6077_);
v___x_6082_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6088_; 
v___x_6083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6083_, 0, v_fst_5986_);
lean_ctor_set(v___x_6083_, 1, v___x_6013_);
v___x_6084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6084_, 0, v_fst_5982_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6085_, 0, v_fst_5978_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6082_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
if (v_isShared_6080_ == 0)
{
lean_ctor_set(v___x_6079_, 0, v___x_6086_);
v___x_6088_ = v___x_6079_;
goto v_reusejp_6087_;
}
else
{
lean_object* v_reuseFailAlloc_6089_; 
v_reuseFailAlloc_6089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6089_, 0, v___x_6086_);
v___x_6088_ = v_reuseFailAlloc_6089_;
goto v_reusejp_6087_;
}
v_reusejp_6087_:
{
return v___x_6088_;
}
}
}
}
else
{
lean_object* v_a_6092_; lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6099_; 
lean_del_object(v___x_6055_);
lean_dec_ref(v___x_6013_);
lean_dec(v_fst_5986_);
lean_dec(v_fst_5982_);
lean_dec(v_fst_5978_);
v_a_6092_ = lean_ctor_get(v___x_6076_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_6076_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6094_ = v___x_6076_;
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
else
{
lean_inc(v_a_6092_);
lean_dec(v___x_6076_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v___x_6097_; 
if (v_isShared_6095_ == 0)
{
v___x_6097_ = v___x_6094_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
v___x_6097_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
return v___x_6097_;
}
}
}
}
}
else
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6107_; 
lean_del_object(v___x_6055_);
lean_dec(v_val_6053_);
lean_dec(v_seq_6019_);
lean_dec_ref(v___x_6013_);
lean_dec(v_start_5990_);
lean_del_object(v___x_5988_);
lean_dec(v_fst_5986_);
lean_del_object(v___x_5984_);
lean_dec(v_fst_5982_);
lean_del_object(v___x_5980_);
lean_dec(v_fst_5978_);
lean_del_object(v___x_5971_);
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v_a_6100_ = lean_ctor_get(v___x_6057_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v___x_6057_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6102_ = v___x_6057_;
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6057_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6105_; 
if (v_isShared_6103_ == 0)
{
v___x_6105_ = v___x_6102_;
goto v_reusejp_6104_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
v___x_6105_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6104_;
}
v_reusejp_6104_:
{
return v___x_6105_;
}
}
}
}
}
else
{
uint8_t v___x_6109_; 
lean_dec(v_a_6052_);
lean_dec(v_start_5990_);
lean_del_object(v___x_5988_);
lean_del_object(v___x_5984_);
lean_del_object(v___x_5980_);
lean_del_object(v___x_5971_);
v___x_6109_ = l_List_isEmpty___redArg(v_seq_6019_);
if (v___x_6109_ == 0)
{
lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6110_ = lean_array_push(v_fst_5978_, v_seq_6019_);
v___x_6111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6111_, 0, v_fst_5986_);
lean_ctor_set(v___x_6111_, 1, v___x_6013_);
v___x_6112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6112_, 0, v_fst_5982_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6110_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_5993_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v_as_x27_5956_ = v_tail_5977_;
v_b_5957_ = v___x_6114_;
goto _start;
}
else
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; 
lean_dec(v_seq_6019_);
v___x_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6116_, 0, v_fst_5986_);
lean_ctor_set(v___x_6116_, 1, v___x_6013_);
v___x_6117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6117_, 0, v_fst_5982_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6118_, 0, v_fst_5978_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_5993_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v_as_x27_5956_ = v_tail_5977_;
v_b_5957_ = v___x_6119_;
goto _start;
}
}
}
else
{
lean_object* v_a_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6128_; 
lean_dec(v_seq_6019_);
lean_dec_ref(v___x_6013_);
lean_dec(v_start_5990_);
lean_del_object(v___x_5988_);
lean_dec(v_fst_5986_);
lean_del_object(v___x_5984_);
lean_dec(v_fst_5982_);
lean_del_object(v___x_5980_);
lean_dec(v_fst_5978_);
lean_del_object(v___x_5971_);
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v_a_6121_ = lean_ctor_get(v___x_6051_, 0);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6051_);
if (v_isSharedCheck_6128_ == 0)
{
v___x_6123_ = v___x_6051_;
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
else
{
lean_inc(v_a_6121_);
lean_dec(v___x_6051_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6126_; 
if (v_isShared_6124_ == 0)
{
v___x_6126_ = v___x_6123_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
v___x_6126_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
return v___x_6126_;
}
}
}
v___jp_6020_:
{
uint8_t v___x_6022_; 
v___x_6022_ = l_List_isEmpty___redArg(v_seq_6019_);
if (v___x_6022_ == 0)
{
lean_object* v___x_6023_; lean_object* v___x_6025_; 
v___x_6023_ = lean_array_push(v_fst_5978_, v_seq_6019_);
if (v_isShared_5989_ == 0)
{
lean_ctor_set(v___x_5988_, 1, v___x_6013_);
lean_ctor_set(v___x_5988_, 0, v_ncb_x3f_6021_);
v___x_6025_ = v___x_5988_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_ncb_x3f_6021_);
lean_ctor_set(v_reuseFailAlloc_6036_, 1, v___x_6013_);
v___x_6025_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
lean_object* v___x_6027_; 
if (v_isShared_5985_ == 0)
{
lean_ctor_set(v___x_5984_, 1, v___x_6025_);
v___x_6027_ = v___x_5984_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_fst_5982_);
lean_ctor_set(v_reuseFailAlloc_6035_, 1, v___x_6025_);
v___x_6027_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
lean_object* v___x_6029_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v___x_6027_);
lean_ctor_set(v___x_5980_, 0, v___x_6023_);
v___x_6029_ = v___x_5980_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v___x_6023_);
lean_ctor_set(v_reuseFailAlloc_6034_, 1, v___x_6027_);
v___x_6029_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
lean_object* v___x_6031_; 
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_6029_);
lean_ctor_set(v___x_5971_, 0, v___x_5993_);
v___x_6031_ = v___x_5971_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_5993_);
lean_ctor_set(v_reuseFailAlloc_6033_, 1, v___x_6029_);
v___x_6031_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6030_;
}
v_reusejp_6030_:
{
v_as_x27_5956_ = v_tail_5977_;
v_b_5957_ = v___x_6031_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_6038_; 
lean_dec(v_seq_6019_);
if (v_isShared_5989_ == 0)
{
lean_ctor_set(v___x_5988_, 1, v___x_6013_);
lean_ctor_set(v___x_5988_, 0, v_ncb_x3f_6021_);
v___x_6038_ = v___x_5988_;
goto v_reusejp_6037_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v_ncb_x3f_6021_);
lean_ctor_set(v_reuseFailAlloc_6049_, 1, v___x_6013_);
v___x_6038_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6037_;
}
v_reusejp_6037_:
{
lean_object* v___x_6040_; 
if (v_isShared_5985_ == 0)
{
lean_ctor_set(v___x_5984_, 1, v___x_6038_);
v___x_6040_ = v___x_5984_;
goto v_reusejp_6039_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_fst_5982_);
lean_ctor_set(v_reuseFailAlloc_6048_, 1, v___x_6038_);
v___x_6040_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6039_;
}
v_reusejp_6039_:
{
lean_object* v___x_6042_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v___x_6040_);
v___x_6042_ = v___x_5980_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6047_; 
v_reuseFailAlloc_6047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6047_, 0, v_fst_5978_);
lean_ctor_set(v_reuseFailAlloc_6047_, 1, v___x_6040_);
v___x_6042_ = v_reuseFailAlloc_6047_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
lean_object* v___x_6044_; 
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_6042_);
lean_ctor_set(v___x_5971_, 0, v___x_5993_);
v___x_6044_ = v___x_5971_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v___x_5993_);
lean_ctor_set(v_reuseFailAlloc_6046_, 1, v___x_6042_);
v___x_6044_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
v_as_x27_5956_ = v_tail_5977_;
v_b_5957_ = v___x_6044_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_dec(v_start_5990_);
if (lean_obj_tag(v_fst_5986_) == 1)
{
lean_object* v_val_6129_; lean_object* v_snd_6130_; lean_object* v_snd_6131_; lean_object* v_fst_6132_; lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6187_; 
lean_dec_ref_known(v_a_6015_, 1);
lean_del_object(v___x_6017_);
lean_del_object(v___x_5984_);
lean_del_object(v___x_5980_);
lean_del_object(v___x_5971_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v_val_6129_ = lean_ctor_get(v_fst_5986_, 0);
lean_inc(v_val_6129_);
v_snd_6130_ = lean_ctor_get(v_val_6129_, 1);
lean_inc(v_snd_6130_);
v_snd_6131_ = lean_ctor_get(v_snd_6130_, 1);
lean_inc(v_snd_6131_);
v_fst_6132_ = lean_ctor_get(v_val_6129_, 0);
v_isSharedCheck_6187_ = !lean_is_exclusive(v_val_6129_);
if (v_isSharedCheck_6187_ == 0)
{
lean_object* v_unused_6188_; 
v_unused_6188_ = lean_ctor_get(v_val_6129_, 1);
lean_dec(v_unused_6188_);
v___x_6134_ = v_val_6129_;
v_isShared_6135_ = v_isSharedCheck_6187_;
goto v_resetjp_6133_;
}
else
{
lean_inc(v_fst_6132_);
lean_dec(v_val_6129_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6187_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v_fst_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6185_; 
v_fst_6136_ = lean_ctor_get(v_snd_6130_, 0);
v_isSharedCheck_6185_ = !lean_is_exclusive(v_snd_6130_);
if (v_isSharedCheck_6185_ == 0)
{
lean_object* v_unused_6186_; 
v_unused_6186_ = lean_ctor_get(v_snd_6130_, 1);
lean_dec(v_unused_6186_);
v___x_6138_ = v_snd_6130_;
v_isShared_6139_ = v_isSharedCheck_6185_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_fst_6136_);
lean_dec(v_snd_6130_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6185_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
lean_object* v_fst_6140_; lean_object* v_snd_6141_; lean_object* v___x_6143_; uint8_t v_isShared_6144_; uint8_t v_isSharedCheck_6184_; 
v_fst_6140_ = lean_ctor_get(v_snd_6131_, 0);
v_snd_6141_ = lean_ctor_get(v_snd_6131_, 1);
v_isSharedCheck_6184_ = !lean_is_exclusive(v_snd_6131_);
if (v_isSharedCheck_6184_ == 0)
{
v___x_6143_ = v_snd_6131_;
v_isShared_6144_ = v_isSharedCheck_6184_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_snd_6141_);
lean_inc(v_fst_6140_);
lean_dec(v_snd_6131_);
v___x_6143_ = lean_box(0);
v_isShared_6144_ = v_isSharedCheck_6184_;
goto v_resetjp_6142_;
}
v_resetjp_6142_:
{
lean_object* v___x_6145_; 
v___x_6145_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_fst_6132_, v___y_5960_, v___y_5964_, v___y_5966_);
if (lean_obj_tag(v___x_6145_) == 0)
{
lean_object* v___x_6146_; 
lean_dec_ref_known(v___x_6145_, 1);
v___x_6146_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5951_, v_snd_5952_, v___x_5953_, v_fst_6136_, v_fst_6140_, v_snd_6141_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
lean_dec(v_fst_6136_);
if (lean_obj_tag(v___x_6146_) == 0)
{
lean_object* v_a_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6167_; 
v_a_6147_ = lean_ctor_get(v___x_6146_, 0);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6146_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6149_ = v___x_6146_;
v_isShared_6150_ = v_isSharedCheck_6167_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_a_6147_);
lean_dec(v___x_6146_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6167_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v___x_6151_; lean_object* v___x_6153_; 
v___x_6151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6151_, 0, v_a_6147_);
if (v_isShared_6144_ == 0)
{
lean_ctor_set(v___x_6143_, 1, v___x_6013_);
lean_ctor_set(v___x_6143_, 0, v_fst_5986_);
v___x_6153_ = v___x_6143_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_fst_5986_);
lean_ctor_set(v_reuseFailAlloc_6166_, 1, v___x_6013_);
v___x_6153_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
lean_object* v___x_6155_; 
if (v_isShared_6139_ == 0)
{
lean_ctor_set(v___x_6138_, 1, v___x_6153_);
lean_ctor_set(v___x_6138_, 0, v_fst_5982_);
v___x_6155_ = v___x_6138_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_fst_5982_);
lean_ctor_set(v_reuseFailAlloc_6165_, 1, v___x_6153_);
v___x_6155_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
lean_object* v___x_6157_; 
if (v_isShared_6135_ == 0)
{
lean_ctor_set(v___x_6134_, 1, v___x_6155_);
lean_ctor_set(v___x_6134_, 0, v_fst_5978_);
v___x_6157_ = v___x_6134_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v_fst_5978_);
lean_ctor_set(v_reuseFailAlloc_6164_, 1, v___x_6155_);
v___x_6157_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
lean_object* v___x_6159_; 
if (v_isShared_5989_ == 0)
{
lean_ctor_set(v___x_5988_, 1, v___x_6157_);
lean_ctor_set(v___x_5988_, 0, v___x_6151_);
v___x_6159_ = v___x_5988_;
goto v_reusejp_6158_;
}
else
{
lean_object* v_reuseFailAlloc_6163_; 
v_reuseFailAlloc_6163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6163_, 0, v___x_6151_);
lean_ctor_set(v_reuseFailAlloc_6163_, 1, v___x_6157_);
v___x_6159_ = v_reuseFailAlloc_6163_;
goto v_reusejp_6158_;
}
v_reusejp_6158_:
{
lean_object* v___x_6161_; 
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 0, v___x_6159_);
v___x_6161_ = v___x_6149_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6162_; 
v_reuseFailAlloc_6162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6162_, 0, v___x_6159_);
v___x_6161_ = v_reuseFailAlloc_6162_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
return v___x_6161_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6168_; lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6175_; 
lean_del_object(v___x_6143_);
lean_del_object(v___x_6138_);
lean_del_object(v___x_6134_);
lean_dec_ref_known(v_fst_5986_, 1);
lean_dec_ref(v___x_6013_);
lean_del_object(v___x_5988_);
lean_dec(v_fst_5982_);
lean_dec(v_fst_5978_);
v_a_6168_ = lean_ctor_get(v___x_6146_, 0);
v_isSharedCheck_6175_ = !lean_is_exclusive(v___x_6146_);
if (v_isSharedCheck_6175_ == 0)
{
v___x_6170_ = v___x_6146_;
v_isShared_6171_ = v_isSharedCheck_6175_;
goto v_resetjp_6169_;
}
else
{
lean_inc(v_a_6168_);
lean_dec(v___x_6146_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6175_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
lean_object* v___x_6173_; 
if (v_isShared_6171_ == 0)
{
v___x_6173_ = v___x_6170_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_a_6168_);
v___x_6173_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
return v___x_6173_;
}
}
}
}
else
{
lean_object* v_a_6176_; lean_object* v___x_6178_; uint8_t v_isShared_6179_; uint8_t v_isSharedCheck_6183_; 
lean_del_object(v___x_6143_);
lean_dec(v_snd_6141_);
lean_dec(v_fst_6140_);
lean_del_object(v___x_6138_);
lean_dec(v_fst_6136_);
lean_del_object(v___x_6134_);
lean_dec_ref_known(v_fst_5986_, 1);
lean_dec_ref(v___x_6013_);
lean_del_object(v___x_5988_);
lean_dec(v_fst_5982_);
lean_dec(v_fst_5978_);
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
v_a_6176_ = lean_ctor_get(v___x_6145_, 0);
v_isSharedCheck_6183_ = !lean_is_exclusive(v___x_6145_);
if (v_isSharedCheck_6183_ == 0)
{
v___x_6178_ = v___x_6145_;
v_isShared_6179_ = v_isSharedCheck_6183_;
goto v_resetjp_6177_;
}
else
{
lean_inc(v_a_6176_);
lean_dec(v___x_6145_);
v___x_6178_ = lean_box(0);
v_isShared_6179_ = v_isSharedCheck_6183_;
goto v_resetjp_6177_;
}
v_resetjp_6177_:
{
lean_object* v___x_6181_; 
if (v_isShared_6179_ == 0)
{
v___x_6181_ = v___x_6178_;
goto v_reusejp_6180_;
}
else
{
lean_object* v_reuseFailAlloc_6182_; 
v_reuseFailAlloc_6182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_a_6176_);
v___x_6181_ = v_reuseFailAlloc_6182_;
goto v_reusejp_6180_;
}
v_reusejp_6180_:
{
return v___x_6181_;
}
}
}
}
}
}
}
else
{
if (v_stopAtFirstFailure_5954_ == 0)
{
lean_object* v_gs_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6193_; 
lean_del_object(v___x_6017_);
v_gs_6189_ = lean_ctor_get(v_a_6015_, 0);
lean_inc(v_gs_6189_);
lean_dec_ref_known(v_a_6015_, 1);
v___x_6190_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5955_, v_gs_6189_);
v___x_6191_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_5982_, v___x_6190_);
if (v_isShared_5989_ == 0)
{
lean_ctor_set(v___x_5988_, 1, v___x_6013_);
v___x_6193_ = v___x_5988_;
goto v_reusejp_6192_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v_fst_5986_);
lean_ctor_set(v_reuseFailAlloc_6204_, 1, v___x_6013_);
v___x_6193_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6192_;
}
v_reusejp_6192_:
{
lean_object* v___x_6195_; 
if (v_isShared_5985_ == 0)
{
lean_ctor_set(v___x_5984_, 1, v___x_6193_);
lean_ctor_set(v___x_5984_, 0, v___x_6191_);
v___x_6195_ = v___x_5984_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6203_; 
v_reuseFailAlloc_6203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6203_, 0, v___x_6191_);
lean_ctor_set(v_reuseFailAlloc_6203_, 1, v___x_6193_);
v___x_6195_ = v_reuseFailAlloc_6203_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
lean_object* v___x_6197_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v___x_6195_);
v___x_6197_ = v___x_5980_;
goto v_reusejp_6196_;
}
else
{
lean_object* v_reuseFailAlloc_6202_; 
v_reuseFailAlloc_6202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_fst_5978_);
lean_ctor_set(v_reuseFailAlloc_6202_, 1, v___x_6195_);
v___x_6197_ = v_reuseFailAlloc_6202_;
goto v_reusejp_6196_;
}
v_reusejp_6196_:
{
lean_object* v___x_6199_; 
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_6197_);
lean_ctor_set(v___x_5971_, 0, v___x_5993_);
v___x_6199_ = v___x_5971_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6201_; 
v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___x_5993_);
lean_ctor_set(v_reuseFailAlloc_6201_, 1, v___x_6197_);
v___x_6199_ = v_reuseFailAlloc_6201_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
v_as_x27_5956_ = v_tail_5977_;
v_b_5957_ = v___x_6199_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_gs_6205_; lean_object* v___x_6207_; uint8_t v_isShared_6208_; uint8_t v_isSharedCheck_6229_; 
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v_gs_6205_ = lean_ctor_get(v_a_6015_, 0);
v_isSharedCheck_6229_ = !lean_is_exclusive(v_a_6015_);
if (v_isSharedCheck_6229_ == 0)
{
v___x_6207_ = v_a_6015_;
v_isShared_6208_ = v_isSharedCheck_6229_;
goto v_resetjp_6206_;
}
else
{
lean_inc(v_gs_6205_);
lean_dec(v_a_6015_);
v___x_6207_ = lean_box(0);
v_isShared_6208_ = v_isSharedCheck_6229_;
goto v_resetjp_6206_;
}
v_resetjp_6206_:
{
lean_object* v___x_6209_; lean_object* v___x_6211_; 
v___x_6209_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5955_, v_gs_6205_);
if (v_isShared_6208_ == 0)
{
lean_ctor_set(v___x_6207_, 0, v___x_6209_);
v___x_6211_ = v___x_6207_;
goto v_reusejp_6210_;
}
else
{
lean_object* v_reuseFailAlloc_6228_; 
v_reuseFailAlloc_6228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6228_, 0, v___x_6209_);
v___x_6211_ = v_reuseFailAlloc_6228_;
goto v_reusejp_6210_;
}
v_reusejp_6210_:
{
lean_object* v___x_6212_; lean_object* v___x_6214_; 
v___x_6212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6211_);
if (v_isShared_5989_ == 0)
{
lean_ctor_set(v___x_5988_, 1, v___x_6013_);
v___x_6214_ = v___x_5988_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6227_; 
v_reuseFailAlloc_6227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_fst_5986_);
lean_ctor_set(v_reuseFailAlloc_6227_, 1, v___x_6013_);
v___x_6214_ = v_reuseFailAlloc_6227_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
lean_object* v___x_6216_; 
if (v_isShared_5985_ == 0)
{
lean_ctor_set(v___x_5984_, 1, v___x_6214_);
v___x_6216_ = v___x_5984_;
goto v_reusejp_6215_;
}
else
{
lean_object* v_reuseFailAlloc_6226_; 
v_reuseFailAlloc_6226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6226_, 0, v_fst_5982_);
lean_ctor_set(v_reuseFailAlloc_6226_, 1, v___x_6214_);
v___x_6216_ = v_reuseFailAlloc_6226_;
goto v_reusejp_6215_;
}
v_reusejp_6215_:
{
lean_object* v___x_6218_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v___x_6216_);
v___x_6218_ = v___x_5980_;
goto v_reusejp_6217_;
}
else
{
lean_object* v_reuseFailAlloc_6225_; 
v_reuseFailAlloc_6225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6225_, 0, v_fst_5978_);
lean_ctor_set(v_reuseFailAlloc_6225_, 1, v___x_6216_);
v___x_6218_ = v_reuseFailAlloc_6225_;
goto v_reusejp_6217_;
}
v_reusejp_6217_:
{
lean_object* v___x_6220_; 
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_6218_);
lean_ctor_set(v___x_5971_, 0, v___x_6212_);
v___x_6220_ = v___x_5971_;
goto v_reusejp_6219_;
}
else
{
lean_object* v_reuseFailAlloc_6224_; 
v_reuseFailAlloc_6224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6224_, 0, v___x_6212_);
lean_ctor_set(v_reuseFailAlloc_6224_, 1, v___x_6218_);
v___x_6220_ = v_reuseFailAlloc_6224_;
goto v_reusejp_6219_;
}
v_reusejp_6219_:
{
lean_object* v___x_6222_; 
if (v_isShared_6018_ == 0)
{
lean_ctor_set(v___x_6017_, 0, v___x_6220_);
v___x_6222_ = v___x_6017_;
goto v_reusejp_6221_;
}
else
{
lean_object* v_reuseFailAlloc_6223_; 
v_reuseFailAlloc_6223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6223_, 0, v___x_6220_);
v___x_6222_ = v_reuseFailAlloc_6223_;
goto v_reusejp_6221_;
}
v_reusejp_6221_:
{
return v___x_6222_;
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
}
}
else
{
lean_object* v_a_6231_; lean_object* v___x_6233_; uint8_t v_isShared_6234_; uint8_t v_isSharedCheck_6238_; 
lean_dec_ref(v___x_6013_);
lean_dec(v_start_5990_);
lean_del_object(v___x_5988_);
lean_dec(v_fst_5986_);
lean_del_object(v___x_5984_);
lean_dec(v_fst_5982_);
lean_del_object(v___x_5980_);
lean_dec(v_fst_5978_);
lean_del_object(v___x_5971_);
lean_dec(v___x_5953_);
lean_dec_ref(v_snd_5952_);
lean_dec_ref(v_goal_5950_);
lean_dec(v_a_5949_);
lean_dec_ref(v_kp_5948_);
v_a_6231_ = lean_ctor_get(v___x_6014_, 0);
v_isSharedCheck_6238_ = !lean_is_exclusive(v___x_6014_);
if (v_isSharedCheck_6238_ == 0)
{
v___x_6233_ = v___x_6014_;
v_isShared_6234_ = v_isSharedCheck_6238_;
goto v_resetjp_6232_;
}
else
{
lean_inc(v_a_6231_);
lean_dec(v___x_6014_);
v___x_6233_ = lean_box(0);
v_isShared_6234_ = v_isSharedCheck_6238_;
goto v_resetjp_6232_;
}
v_resetjp_6232_:
{
lean_object* v___x_6236_; 
if (v_isShared_6234_ == 0)
{
v___x_6236_ = v___x_6233_;
goto v_reusejp_6235_;
}
else
{
lean_object* v_reuseFailAlloc_6237_; 
v_reuseFailAlloc_6237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6237_, 0, v_a_6231_);
v___x_6236_ = v_reuseFailAlloc_6237_;
goto v_reusejp_6235_;
}
v_reusejp_6235_:
{
return v___x_6236_;
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object** _args){
lean_object* v_kp_6252_ = _args[0];
lean_object* v_a_6253_ = _args[1];
lean_object* v_goal_6254_ = _args[2];
lean_object* v___x_6255_ = _args[3];
lean_object* v_snd_6256_ = _args[4];
lean_object* v___x_6257_ = _args[5];
lean_object* v_stopAtFirstFailure_6258_ = _args[6];
lean_object* v___x_6259_ = _args[7];
lean_object* v_as_x27_6260_ = _args[8];
lean_object* v_b_6261_ = _args[9];
lean_object* v___y_6262_ = _args[10];
lean_object* v___y_6263_ = _args[11];
lean_object* v___y_6264_ = _args[12];
lean_object* v___y_6265_ = _args[13];
lean_object* v___y_6266_ = _args[14];
lean_object* v___y_6267_ = _args[15];
lean_object* v___y_6268_ = _args[16];
lean_object* v___y_6269_ = _args[17];
lean_object* v___y_6270_ = _args[18];
lean_object* v___y_6271_ = _args[19];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6272_; lean_object* v_res_6273_; 
v_stopAtFirstFailure_boxed_6272_ = lean_unbox(v_stopAtFirstFailure_6258_);
v_res_6273_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6252_, v_a_6253_, v_goal_6254_, v___x_6255_, v_snd_6256_, v___x_6257_, v_stopAtFirstFailure_boxed_6272_, v___x_6259_, v_as_x27_6260_, v_b_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
lean_dec(v___y_6262_);
lean_dec(v_as_x27_6260_);
lean_dec_ref(v___x_6259_);
lean_dec(v___x_6255_);
return v_res_6273_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v___x_6274_, lean_object* v_c_6275_, lean_object* v___x_6276_, lean_object* v___x_6277_, lean_object* v___x_6278_, uint64_t v_a_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_){
_start:
{
if (lean_obj_tag(v_a_6280_) == 0)
{
lean_object* v___x_6282_; 
lean_dec_ref(v___x_6278_);
lean_dec(v___x_6277_);
lean_dec_ref(v___x_6276_);
lean_dec_ref(v___x_6274_);
v___x_6282_ = lean_array_to_list(v_a_6281_);
return v___x_6282_;
}
else
{
lean_object* v_split_6283_; lean_object* v_head_6284_; lean_object* v_tail_6285_; lean_object* v___x_6287_; uint8_t v_isShared_6288_; uint8_t v_isSharedCheck_6336_; 
v_split_6283_ = lean_ctor_get(v___x_6274_, 15);
lean_inc_ref(v_split_6283_);
v_head_6284_ = lean_ctor_get(v_a_6280_, 0);
v_tail_6285_ = lean_ctor_get(v_a_6280_, 1);
v_isSharedCheck_6336_ = !lean_is_exclusive(v_a_6280_);
if (v_isSharedCheck_6336_ == 0)
{
v___x_6287_ = v_a_6280_;
v_isShared_6288_ = v_isSharedCheck_6336_;
goto v_resetjp_6286_;
}
else
{
lean_inc(v_tail_6285_);
lean_inc(v_head_6284_);
lean_dec(v_a_6280_);
v___x_6287_ = lean_box(0);
v_isShared_6288_ = v_isSharedCheck_6336_;
goto v_resetjp_6286_;
}
v_resetjp_6286_:
{
lean_object* v_nextDeclIdx_6289_; lean_object* v_enodeMap_6290_; lean_object* v_exprs_6291_; lean_object* v_parents_6292_; lean_object* v_congrTable_6293_; lean_object* v_appMap_6294_; lean_object* v_indicesFound_6295_; lean_object* v_toProcess_6296_; lean_object* v_internalizing_6297_; uint8_t v_inconsistent_6298_; lean_object* v_nextIdx_6299_; lean_object* v_newRawFacts_6300_; lean_object* v_facts_6301_; lean_object* v_extThms_6302_; lean_object* v_ematch_6303_; lean_object* v_inj_6304_; lean_object* v_clean_6305_; lean_object* v_sstates_6306_; uint64_t v_introBase_6307_; lean_object* v_numIntros_6308_; lean_object* v_candidates_6309_; lean_object* v_added_6310_; lean_object* v_resolved_6311_; lean_object* v_trace_6312_; lean_object* v_lookaheads_6313_; lean_object* v_argPosMap_6314_; lean_object* v_argsAt_6315_; lean_object* v___x_6317_; uint8_t v_isShared_6318_; uint8_t v_isSharedCheck_6335_; 
v_nextDeclIdx_6289_ = lean_ctor_get(v___x_6274_, 0);
v_enodeMap_6290_ = lean_ctor_get(v___x_6274_, 1);
v_exprs_6291_ = lean_ctor_get(v___x_6274_, 2);
v_parents_6292_ = lean_ctor_get(v___x_6274_, 3);
v_congrTable_6293_ = lean_ctor_get(v___x_6274_, 4);
v_appMap_6294_ = lean_ctor_get(v___x_6274_, 5);
v_indicesFound_6295_ = lean_ctor_get(v___x_6274_, 6);
v_toProcess_6296_ = lean_ctor_get(v___x_6274_, 7);
v_internalizing_6297_ = lean_ctor_get(v___x_6274_, 8);
v_inconsistent_6298_ = lean_ctor_get_uint8(v___x_6274_, sizeof(void*)*20 + 8);
v_nextIdx_6299_ = lean_ctor_get(v___x_6274_, 9);
v_newRawFacts_6300_ = lean_ctor_get(v___x_6274_, 10);
v_facts_6301_ = lean_ctor_get(v___x_6274_, 11);
v_extThms_6302_ = lean_ctor_get(v___x_6274_, 12);
v_ematch_6303_ = lean_ctor_get(v___x_6274_, 13);
v_inj_6304_ = lean_ctor_get(v___x_6274_, 14);
v_clean_6305_ = lean_ctor_get(v___x_6274_, 16);
v_sstates_6306_ = lean_ctor_get(v___x_6274_, 17);
v_introBase_6307_ = lean_ctor_get_uint64(v___x_6274_, sizeof(void*)*20);
v_numIntros_6308_ = lean_ctor_get(v___x_6274_, 19);
v_candidates_6309_ = lean_ctor_get(v_split_6283_, 0);
v_added_6310_ = lean_ctor_get(v_split_6283_, 1);
v_resolved_6311_ = lean_ctor_get(v_split_6283_, 2);
v_trace_6312_ = lean_ctor_get(v_split_6283_, 3);
v_lookaheads_6313_ = lean_ctor_get(v_split_6283_, 4);
v_argPosMap_6314_ = lean_ctor_get(v_split_6283_, 5);
v_argsAt_6315_ = lean_ctor_get(v_split_6283_, 6);
v_isSharedCheck_6335_ = !lean_is_exclusive(v_split_6283_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6317_ = v_split_6283_;
v_isShared_6318_ = v_isSharedCheck_6335_;
goto v_resetjp_6316_;
}
else
{
lean_inc(v_argsAt_6315_);
lean_inc(v_argPosMap_6314_);
lean_inc(v_lookaheads_6313_);
lean_inc(v_trace_6312_);
lean_inc(v_resolved_6311_);
lean_inc(v_added_6310_);
lean_inc(v_candidates_6309_);
lean_dec(v_split_6283_);
v___x_6317_ = lean_box(0);
v_isShared_6318_ = v_isSharedCheck_6335_;
goto v_resetjp_6316_;
}
v_resetjp_6316_:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6323_; 
v___x_6319_ = lean_array_get_size(v_a_6281_);
v___x_6320_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_6275_);
lean_inc(v___x_6277_);
lean_inc_ref(v___x_6276_);
v___x_6321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6321_, 0, v___x_6276_);
lean_ctor_set(v___x_6321_, 1, v___x_6319_);
lean_ctor_set(v___x_6321_, 2, v___x_6277_);
lean_ctor_set(v___x_6321_, 3, v___x_6320_);
if (v_isShared_6288_ == 0)
{
lean_ctor_set(v___x_6287_, 1, v_trace_6312_);
lean_ctor_set(v___x_6287_, 0, v___x_6321_);
v___x_6323_ = v___x_6287_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v___x_6321_);
lean_ctor_set(v_reuseFailAlloc_6334_, 1, v_trace_6312_);
v___x_6323_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
lean_object* v___x_6325_; 
if (v_isShared_6318_ == 0)
{
lean_ctor_set(v___x_6317_, 3, v___x_6323_);
v___x_6325_ = v___x_6317_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6333_; 
v_reuseFailAlloc_6333_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_candidates_6309_);
lean_ctor_set(v_reuseFailAlloc_6333_, 1, v_added_6310_);
lean_ctor_set(v_reuseFailAlloc_6333_, 2, v_resolved_6311_);
lean_ctor_set(v_reuseFailAlloc_6333_, 3, v___x_6323_);
lean_ctor_set(v_reuseFailAlloc_6333_, 4, v_lookaheads_6313_);
lean_ctor_set(v_reuseFailAlloc_6333_, 5, v_argPosMap_6314_);
lean_ctor_set(v_reuseFailAlloc_6333_, 6, v_argsAt_6315_);
v___x_6325_ = v_reuseFailAlloc_6333_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; uint64_t v___x_6328_; uint64_t v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
lean_inc(v_numIntros_6308_);
lean_inc_ref(v___x_6278_);
lean_inc_ref(v_sstates_6306_);
lean_inc_ref(v_clean_6305_);
lean_inc_ref(v_inj_6304_);
lean_inc_ref(v_ematch_6303_);
lean_inc_ref(v_extThms_6302_);
lean_inc_ref(v_facts_6301_);
lean_inc_ref(v_newRawFacts_6300_);
lean_inc(v_nextIdx_6299_);
lean_inc_ref(v_internalizing_6297_);
lean_inc_ref(v_toProcess_6296_);
lean_inc_ref(v_indicesFound_6295_);
lean_inc_ref(v_appMap_6294_);
lean_inc_ref(v_congrTable_6293_);
lean_inc_ref(v_parents_6292_);
lean_inc_ref(v_exprs_6291_);
lean_inc_ref(v_enodeMap_6290_);
lean_inc(v_nextDeclIdx_6289_);
v___x_6326_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v___x_6326_, 0, v_nextDeclIdx_6289_);
lean_ctor_set(v___x_6326_, 1, v_enodeMap_6290_);
lean_ctor_set(v___x_6326_, 2, v_exprs_6291_);
lean_ctor_set(v___x_6326_, 3, v_parents_6292_);
lean_ctor_set(v___x_6326_, 4, v_congrTable_6293_);
lean_ctor_set(v___x_6326_, 5, v_appMap_6294_);
lean_ctor_set(v___x_6326_, 6, v_indicesFound_6295_);
lean_ctor_set(v___x_6326_, 7, v_toProcess_6296_);
lean_ctor_set(v___x_6326_, 8, v_internalizing_6297_);
lean_ctor_set(v___x_6326_, 9, v_nextIdx_6299_);
lean_ctor_set(v___x_6326_, 10, v_newRawFacts_6300_);
lean_ctor_set(v___x_6326_, 11, v_facts_6301_);
lean_ctor_set(v___x_6326_, 12, v_extThms_6302_);
lean_ctor_set(v___x_6326_, 13, v_ematch_6303_);
lean_ctor_set(v___x_6326_, 14, v_inj_6304_);
lean_ctor_set(v___x_6326_, 15, v___x_6325_);
lean_ctor_set(v___x_6326_, 16, v_clean_6305_);
lean_ctor_set(v___x_6326_, 17, v_sstates_6306_);
lean_ctor_set(v___x_6326_, 18, v___x_6278_);
lean_ctor_set(v___x_6326_, 19, v_numIntros_6308_);
lean_ctor_set_uint8(v___x_6326_, sizeof(void*)*20 + 8, v_inconsistent_6298_);
lean_ctor_set_uint64(v___x_6326_, sizeof(void*)*20, v_introBase_6307_);
v___x_6327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6327_, 0, v___x_6326_);
lean_ctor_set(v___x_6327_, 1, v_head_6284_);
v___x_6328_ = lean_uint64_of_nat(v___x_6319_);
v___x_6329_ = lean_uint64_mix_hash(v_a_6279_, v___x_6328_);
v___x_6330_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_6327_, v___x_6329_);
v___x_6331_ = lean_array_push(v_a_6281_, v___x_6330_);
v_a_6280_ = v_tail_6285_;
v_a_6281_ = v___x_6331_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v___x_6337_, lean_object* v_c_6338_, lean_object* v___x_6339_, lean_object* v___x_6340_, lean_object* v___x_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_){
_start:
{
uint64_t v_a_118059__boxed_6345_; lean_object* v_res_6346_; 
v_a_118059__boxed_6345_ = lean_unbox_uint64(v_a_6342_);
lean_dec_ref(v_a_6342_);
v_res_6346_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_6337_, v_c_6338_, v___x_6339_, v___x_6340_, v___x_6341_, v_a_118059__boxed_6345_, v_a_6343_, v_a_6344_);
lean_dec_ref(v_c_6338_);
return v_res_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_6347_, lean_object* v_x_6348_, lean_object* v_x_6349_, lean_object* v_x_6350_){
_start:
{
lean_object* v_ks_6351_; lean_object* v_vs_6352_; lean_object* v___x_6354_; uint8_t v_isShared_6355_; uint8_t v_isSharedCheck_6376_; 
v_ks_6351_ = lean_ctor_get(v_x_6347_, 0);
v_vs_6352_ = lean_ctor_get(v_x_6347_, 1);
v_isSharedCheck_6376_ = !lean_is_exclusive(v_x_6347_);
if (v_isSharedCheck_6376_ == 0)
{
v___x_6354_ = v_x_6347_;
v_isShared_6355_ = v_isSharedCheck_6376_;
goto v_resetjp_6353_;
}
else
{
lean_inc(v_vs_6352_);
lean_inc(v_ks_6351_);
lean_dec(v_x_6347_);
v___x_6354_ = lean_box(0);
v_isShared_6355_ = v_isSharedCheck_6376_;
goto v_resetjp_6353_;
}
v_resetjp_6353_:
{
lean_object* v___x_6356_; uint8_t v___x_6357_; 
v___x_6356_ = lean_array_get_size(v_ks_6351_);
v___x_6357_ = lean_nat_dec_lt(v_x_6348_, v___x_6356_);
if (v___x_6357_ == 0)
{
lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6361_; 
lean_dec(v_x_6348_);
v___x_6358_ = lean_array_push(v_ks_6351_, v_x_6349_);
v___x_6359_ = lean_array_push(v_vs_6352_, v_x_6350_);
if (v_isShared_6355_ == 0)
{
lean_ctor_set(v___x_6354_, 1, v___x_6359_);
lean_ctor_set(v___x_6354_, 0, v___x_6358_);
v___x_6361_ = v___x_6354_;
goto v_reusejp_6360_;
}
else
{
lean_object* v_reuseFailAlloc_6362_; 
v_reuseFailAlloc_6362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6362_, 0, v___x_6358_);
lean_ctor_set(v_reuseFailAlloc_6362_, 1, v___x_6359_);
v___x_6361_ = v_reuseFailAlloc_6362_;
goto v_reusejp_6360_;
}
v_reusejp_6360_:
{
return v___x_6361_;
}
}
else
{
lean_object* v_k_x27_6363_; uint8_t v___x_6364_; 
v_k_x27_6363_ = lean_array_fget_borrowed(v_ks_6351_, v_x_6348_);
v___x_6364_ = l_Lean_instBEqMVarId_beq(v_x_6349_, v_k_x27_6363_);
if (v___x_6364_ == 0)
{
lean_object* v___x_6366_; 
if (v_isShared_6355_ == 0)
{
v___x_6366_ = v___x_6354_;
goto v_reusejp_6365_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v_ks_6351_);
lean_ctor_set(v_reuseFailAlloc_6370_, 1, v_vs_6352_);
v___x_6366_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6365_;
}
v_reusejp_6365_:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6367_ = lean_unsigned_to_nat(1u);
v___x_6368_ = lean_nat_add(v_x_6348_, v___x_6367_);
lean_dec(v_x_6348_);
v_x_6347_ = v___x_6366_;
v_x_6348_ = v___x_6368_;
goto _start;
}
}
else
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6374_; 
v___x_6371_ = lean_array_fset(v_ks_6351_, v_x_6348_, v_x_6349_);
v___x_6372_ = lean_array_fset(v_vs_6352_, v_x_6348_, v_x_6350_);
lean_dec(v_x_6348_);
if (v_isShared_6355_ == 0)
{
lean_ctor_set(v___x_6354_, 1, v___x_6372_);
lean_ctor_set(v___x_6354_, 0, v___x_6371_);
v___x_6374_ = v___x_6354_;
goto v_reusejp_6373_;
}
else
{
lean_object* v_reuseFailAlloc_6375_; 
v_reuseFailAlloc_6375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6375_, 0, v___x_6371_);
lean_ctor_set(v_reuseFailAlloc_6375_, 1, v___x_6372_);
v___x_6374_ = v_reuseFailAlloc_6375_;
goto v_reusejp_6373_;
}
v_reusejp_6373_:
{
return v___x_6374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(lean_object* v_n_6377_, lean_object* v_k_6378_, lean_object* v_v_6379_){
_start:
{
lean_object* v___x_6380_; lean_object* v___x_6381_; 
v___x_6380_ = lean_unsigned_to_nat(0u);
v___x_6381_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_n_6377_, v___x_6380_, v_k_6378_, v_v_6379_);
return v___x_6381_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_6382_; 
v___x_6382_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_6382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(lean_object* v_x_6383_, size_t v_x_6384_, size_t v_x_6385_, lean_object* v_x_6386_, lean_object* v_x_6387_){
_start:
{
if (lean_obj_tag(v_x_6383_) == 0)
{
lean_object* v_es_6388_; size_t v___x_6389_; size_t v___x_6390_; lean_object* v_j_6391_; lean_object* v___x_6392_; uint8_t v___x_6393_; 
v_es_6388_ = lean_ctor_get(v_x_6383_, 0);
v___x_6389_ = ((size_t)31ULL);
v___x_6390_ = lean_usize_land(v_x_6384_, v___x_6389_);
v_j_6391_ = lean_usize_to_nat(v___x_6390_);
v___x_6392_ = lean_array_get_size(v_es_6388_);
v___x_6393_ = lean_nat_dec_lt(v_j_6391_, v___x_6392_);
if (v___x_6393_ == 0)
{
lean_dec(v_j_6391_);
lean_dec(v_x_6387_);
lean_dec(v_x_6386_);
return v_x_6383_;
}
else
{
lean_object* v___x_6395_; uint8_t v_isShared_6396_; uint8_t v_isSharedCheck_6432_; 
lean_inc_ref(v_es_6388_);
v_isSharedCheck_6432_ = !lean_is_exclusive(v_x_6383_);
if (v_isSharedCheck_6432_ == 0)
{
lean_object* v_unused_6433_; 
v_unused_6433_ = lean_ctor_get(v_x_6383_, 0);
lean_dec(v_unused_6433_);
v___x_6395_ = v_x_6383_;
v_isShared_6396_ = v_isSharedCheck_6432_;
goto v_resetjp_6394_;
}
else
{
lean_dec(v_x_6383_);
v___x_6395_ = lean_box(0);
v_isShared_6396_ = v_isSharedCheck_6432_;
goto v_resetjp_6394_;
}
v_resetjp_6394_:
{
lean_object* v_v_6397_; lean_object* v___x_6398_; lean_object* v_xs_x27_6399_; lean_object* v___y_6401_; 
v_v_6397_ = lean_array_fget(v_es_6388_, v_j_6391_);
v___x_6398_ = lean_box(0);
v_xs_x27_6399_ = lean_array_fset(v_es_6388_, v_j_6391_, v___x_6398_);
switch(lean_obj_tag(v_v_6397_))
{
case 0:
{
lean_object* v_key_6406_; lean_object* v_val_6407_; lean_object* v___x_6409_; uint8_t v_isShared_6410_; uint8_t v_isSharedCheck_6417_; 
v_key_6406_ = lean_ctor_get(v_v_6397_, 0);
v_val_6407_ = lean_ctor_get(v_v_6397_, 1);
v_isSharedCheck_6417_ = !lean_is_exclusive(v_v_6397_);
if (v_isSharedCheck_6417_ == 0)
{
v___x_6409_ = v_v_6397_;
v_isShared_6410_ = v_isSharedCheck_6417_;
goto v_resetjp_6408_;
}
else
{
lean_inc(v_val_6407_);
lean_inc(v_key_6406_);
lean_dec(v_v_6397_);
v___x_6409_ = lean_box(0);
v_isShared_6410_ = v_isSharedCheck_6417_;
goto v_resetjp_6408_;
}
v_resetjp_6408_:
{
uint8_t v___x_6411_; 
v___x_6411_ = l_Lean_instBEqMVarId_beq(v_x_6386_, v_key_6406_);
if (v___x_6411_ == 0)
{
lean_object* v___x_6412_; lean_object* v___x_6413_; 
lean_del_object(v___x_6409_);
v___x_6412_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_6406_, v_val_6407_, v_x_6386_, v_x_6387_);
v___x_6413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6413_, 0, v___x_6412_);
v___y_6401_ = v___x_6413_;
goto v___jp_6400_;
}
else
{
lean_object* v___x_6415_; 
lean_dec(v_val_6407_);
lean_dec(v_key_6406_);
if (v_isShared_6410_ == 0)
{
lean_ctor_set(v___x_6409_, 1, v_x_6387_);
lean_ctor_set(v___x_6409_, 0, v_x_6386_);
v___x_6415_ = v___x_6409_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6416_; 
v_reuseFailAlloc_6416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6416_, 0, v_x_6386_);
lean_ctor_set(v_reuseFailAlloc_6416_, 1, v_x_6387_);
v___x_6415_ = v_reuseFailAlloc_6416_;
goto v_reusejp_6414_;
}
v_reusejp_6414_:
{
v___y_6401_ = v___x_6415_;
goto v___jp_6400_;
}
}
}
}
case 1:
{
lean_object* v_node_6418_; lean_object* v___x_6420_; uint8_t v_isShared_6421_; uint8_t v_isSharedCheck_6430_; 
v_node_6418_ = lean_ctor_get(v_v_6397_, 0);
v_isSharedCheck_6430_ = !lean_is_exclusive(v_v_6397_);
if (v_isSharedCheck_6430_ == 0)
{
v___x_6420_ = v_v_6397_;
v_isShared_6421_ = v_isSharedCheck_6430_;
goto v_resetjp_6419_;
}
else
{
lean_inc(v_node_6418_);
lean_dec(v_v_6397_);
v___x_6420_ = lean_box(0);
v_isShared_6421_ = v_isSharedCheck_6430_;
goto v_resetjp_6419_;
}
v_resetjp_6419_:
{
size_t v___x_6422_; size_t v___x_6423_; size_t v___x_6424_; size_t v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6428_; 
v___x_6422_ = ((size_t)5ULL);
v___x_6423_ = lean_usize_shift_right(v_x_6384_, v___x_6422_);
v___x_6424_ = ((size_t)1ULL);
v___x_6425_ = lean_usize_add(v_x_6385_, v___x_6424_);
v___x_6426_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_node_6418_, v___x_6423_, v___x_6425_, v_x_6386_, v_x_6387_);
if (v_isShared_6421_ == 0)
{
lean_ctor_set(v___x_6420_, 0, v___x_6426_);
v___x_6428_ = v___x_6420_;
goto v_reusejp_6427_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v___x_6426_);
v___x_6428_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6427_;
}
v_reusejp_6427_:
{
v___y_6401_ = v___x_6428_;
goto v___jp_6400_;
}
}
}
default: 
{
lean_object* v___x_6431_; 
v___x_6431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6431_, 0, v_x_6386_);
lean_ctor_set(v___x_6431_, 1, v_x_6387_);
v___y_6401_ = v___x_6431_;
goto v___jp_6400_;
}
}
v___jp_6400_:
{
lean_object* v___x_6402_; lean_object* v___x_6404_; 
v___x_6402_ = lean_array_fset(v_xs_x27_6399_, v_j_6391_, v___y_6401_);
lean_dec(v_j_6391_);
if (v_isShared_6396_ == 0)
{
lean_ctor_set(v___x_6395_, 0, v___x_6402_);
v___x_6404_ = v___x_6395_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v___x_6402_);
v___x_6404_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
return v___x_6404_;
}
}
}
}
}
else
{
lean_object* v_ks_6434_; lean_object* v_vs_6435_; lean_object* v___x_6437_; uint8_t v_isShared_6438_; uint8_t v_isSharedCheck_6453_; 
v_ks_6434_ = lean_ctor_get(v_x_6383_, 0);
v_vs_6435_ = lean_ctor_get(v_x_6383_, 1);
v_isSharedCheck_6453_ = !lean_is_exclusive(v_x_6383_);
if (v_isSharedCheck_6453_ == 0)
{
v___x_6437_ = v_x_6383_;
v_isShared_6438_ = v_isSharedCheck_6453_;
goto v_resetjp_6436_;
}
else
{
lean_inc(v_vs_6435_);
lean_inc(v_ks_6434_);
lean_dec(v_x_6383_);
v___x_6437_ = lean_box(0);
v_isShared_6438_ = v_isSharedCheck_6453_;
goto v_resetjp_6436_;
}
v_resetjp_6436_:
{
lean_object* v___x_6440_; 
if (v_isShared_6438_ == 0)
{
v___x_6440_ = v___x_6437_;
goto v_reusejp_6439_;
}
else
{
lean_object* v_reuseFailAlloc_6452_; 
v_reuseFailAlloc_6452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6452_, 0, v_ks_6434_);
lean_ctor_set(v_reuseFailAlloc_6452_, 1, v_vs_6435_);
v___x_6440_ = v_reuseFailAlloc_6452_;
goto v_reusejp_6439_;
}
v_reusejp_6439_:
{
lean_object* v_newNode_6441_; size_t v___x_6442_; uint8_t v___x_6443_; 
v_newNode_6441_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v___x_6440_, v_x_6386_, v_x_6387_);
v___x_6442_ = ((size_t)7ULL);
v___x_6443_ = lean_usize_dec_le(v___x_6442_, v_x_6385_);
if (v___x_6443_ == 0)
{
lean_object* v___x_6444_; lean_object* v___x_6445_; uint8_t v___x_6446_; 
v___x_6444_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_6441_);
v___x_6445_ = lean_unsigned_to_nat(4u);
v___x_6446_ = lean_nat_dec_lt(v___x_6444_, v___x_6445_);
lean_dec(v___x_6444_);
if (v___x_6446_ == 0)
{
lean_object* v_ks_6447_; lean_object* v_vs_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v_ks_6447_ = lean_ctor_get(v_newNode_6441_, 0);
lean_inc_ref(v_ks_6447_);
v_vs_6448_ = lean_ctor_get(v_newNode_6441_, 1);
lean_inc_ref(v_vs_6448_);
lean_dec_ref(v_newNode_6441_);
v___x_6449_ = lean_unsigned_to_nat(0u);
v___x_6450_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0);
v___x_6451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_x_6385_, v_ks_6447_, v_vs_6448_, v___x_6449_, v___x_6450_);
lean_dec_ref(v_vs_6448_);
lean_dec_ref(v_ks_6447_);
return v___x_6451_;
}
else
{
return v_newNode_6441_;
}
}
else
{
return v_newNode_6441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(size_t v_depth_6454_, lean_object* v_keys_6455_, lean_object* v_vals_6456_, lean_object* v_i_6457_, lean_object* v_entries_6458_){
_start:
{
lean_object* v___x_6459_; uint8_t v___x_6460_; 
v___x_6459_ = lean_array_get_size(v_keys_6455_);
v___x_6460_ = lean_nat_dec_lt(v_i_6457_, v___x_6459_);
if (v___x_6460_ == 0)
{
lean_dec(v_i_6457_);
return v_entries_6458_;
}
else
{
lean_object* v_k_6461_; lean_object* v_v_6462_; uint64_t v___x_6463_; size_t v_h_6464_; size_t v___x_6465_; lean_object* v___x_6466_; size_t v___x_6467_; size_t v___x_6468_; size_t v___x_6469_; size_t v_h_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v_k_6461_ = lean_array_fget_borrowed(v_keys_6455_, v_i_6457_);
v_v_6462_ = lean_array_fget_borrowed(v_vals_6456_, v_i_6457_);
v___x_6463_ = l_Lean_instHashableMVarId_hash(v_k_6461_);
v_h_6464_ = lean_uint64_to_usize(v___x_6463_);
v___x_6465_ = ((size_t)5ULL);
v___x_6466_ = lean_unsigned_to_nat(1u);
v___x_6467_ = ((size_t)1ULL);
v___x_6468_ = lean_usize_sub(v_depth_6454_, v___x_6467_);
v___x_6469_ = lean_usize_mul(v___x_6465_, v___x_6468_);
v_h_6470_ = lean_usize_shift_right(v_h_6464_, v___x_6469_);
v___x_6471_ = lean_nat_add(v_i_6457_, v___x_6466_);
lean_dec(v_i_6457_);
lean_inc(v_v_6462_);
lean_inc(v_k_6461_);
v___x_6472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_entries_6458_, v_h_6470_, v_depth_6454_, v_k_6461_, v_v_6462_);
v_i_6457_ = v___x_6471_;
v_entries_6458_ = v___x_6472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_depth_6474_, lean_object* v_keys_6475_, lean_object* v_vals_6476_, lean_object* v_i_6477_, lean_object* v_entries_6478_){
_start:
{
size_t v_depth_boxed_6479_; lean_object* v_res_6480_; 
v_depth_boxed_6479_ = lean_unbox_usize(v_depth_6474_);
lean_dec(v_depth_6474_);
v_res_6480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_boxed_6479_, v_keys_6475_, v_vals_6476_, v_i_6477_, v_entries_6478_);
lean_dec_ref(v_vals_6476_);
lean_dec_ref(v_keys_6475_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_x_6481_, lean_object* v_x_6482_, lean_object* v_x_6483_, lean_object* v_x_6484_, lean_object* v_x_6485_){
_start:
{
size_t v_x_118207__boxed_6486_; size_t v_x_118208__boxed_6487_; lean_object* v_res_6488_; 
v_x_118207__boxed_6486_ = lean_unbox_usize(v_x_6482_);
lean_dec(v_x_6482_);
v_x_118208__boxed_6487_ = lean_unbox_usize(v_x_6483_);
lean_dec(v_x_6483_);
v_res_6488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6481_, v_x_118207__boxed_6486_, v_x_118208__boxed_6487_, v_x_6484_, v_x_6485_);
return v_res_6488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(lean_object* v_x_6489_, lean_object* v_x_6490_, lean_object* v_x_6491_){
_start:
{
uint64_t v___x_6492_; size_t v___x_6493_; size_t v___x_6494_; lean_object* v___x_6495_; 
v___x_6492_ = l_Lean_instHashableMVarId_hash(v_x_6490_);
v___x_6493_ = lean_uint64_to_usize(v___x_6492_);
v___x_6494_ = ((size_t)1ULL);
v___x_6495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6489_, v___x_6493_, v___x_6494_, v_x_6490_, v_x_6491_);
return v___x_6495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_mvarId_6496_, lean_object* v_val_6497_, lean_object* v___y_6498_){
_start:
{
lean_object* v___x_6500_; lean_object* v_mctx_6501_; lean_object* v_cache_6502_; lean_object* v_zetaDeltaFVarIds_6503_; lean_object* v_postponed_6504_; lean_object* v_diag_6505_; lean_object* v___x_6507_; uint8_t v_isShared_6508_; uint8_t v_isSharedCheck_6534_; 
v___x_6500_ = lean_st_ref_take(v___y_6498_);
v_mctx_6501_ = lean_ctor_get(v___x_6500_, 0);
v_cache_6502_ = lean_ctor_get(v___x_6500_, 1);
v_zetaDeltaFVarIds_6503_ = lean_ctor_get(v___x_6500_, 2);
v_postponed_6504_ = lean_ctor_get(v___x_6500_, 3);
v_diag_6505_ = lean_ctor_get(v___x_6500_, 4);
v_isSharedCheck_6534_ = !lean_is_exclusive(v___x_6500_);
if (v_isSharedCheck_6534_ == 0)
{
v___x_6507_ = v___x_6500_;
v_isShared_6508_ = v_isSharedCheck_6534_;
goto v_resetjp_6506_;
}
else
{
lean_inc(v_diag_6505_);
lean_inc(v_postponed_6504_);
lean_inc(v_zetaDeltaFVarIds_6503_);
lean_inc(v_cache_6502_);
lean_inc(v_mctx_6501_);
lean_dec(v___x_6500_);
v___x_6507_ = lean_box(0);
v_isShared_6508_ = v_isSharedCheck_6534_;
goto v_resetjp_6506_;
}
v_resetjp_6506_:
{
lean_object* v_depth_6509_; lean_object* v_levelAssignDepth_6510_; lean_object* v_lmvarCounter_6511_; lean_object* v_mvarCounter_6512_; lean_object* v_lDecls_6513_; lean_object* v_decls_6514_; lean_object* v_userNames_6515_; lean_object* v_lAssignment_6516_; lean_object* v_eAssignment_6517_; lean_object* v_dAssignment_6518_; lean_object* v_instanceTypedMVars_6519_; lean_object* v___x_6521_; uint8_t v_isShared_6522_; uint8_t v_isSharedCheck_6533_; 
v_depth_6509_ = lean_ctor_get(v_mctx_6501_, 0);
v_levelAssignDepth_6510_ = lean_ctor_get(v_mctx_6501_, 1);
v_lmvarCounter_6511_ = lean_ctor_get(v_mctx_6501_, 2);
v_mvarCounter_6512_ = lean_ctor_get(v_mctx_6501_, 3);
v_lDecls_6513_ = lean_ctor_get(v_mctx_6501_, 4);
v_decls_6514_ = lean_ctor_get(v_mctx_6501_, 5);
v_userNames_6515_ = lean_ctor_get(v_mctx_6501_, 6);
v_lAssignment_6516_ = lean_ctor_get(v_mctx_6501_, 7);
v_eAssignment_6517_ = lean_ctor_get(v_mctx_6501_, 8);
v_dAssignment_6518_ = lean_ctor_get(v_mctx_6501_, 9);
v_instanceTypedMVars_6519_ = lean_ctor_get(v_mctx_6501_, 10);
v_isSharedCheck_6533_ = !lean_is_exclusive(v_mctx_6501_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6521_ = v_mctx_6501_;
v_isShared_6522_ = v_isSharedCheck_6533_;
goto v_resetjp_6520_;
}
else
{
lean_inc(v_instanceTypedMVars_6519_);
lean_inc(v_dAssignment_6518_);
lean_inc(v_eAssignment_6517_);
lean_inc(v_lAssignment_6516_);
lean_inc(v_userNames_6515_);
lean_inc(v_decls_6514_);
lean_inc(v_lDecls_6513_);
lean_inc(v_mvarCounter_6512_);
lean_inc(v_lmvarCounter_6511_);
lean_inc(v_levelAssignDepth_6510_);
lean_inc(v_depth_6509_);
lean_dec(v_mctx_6501_);
v___x_6521_ = lean_box(0);
v_isShared_6522_ = v_isSharedCheck_6533_;
goto v_resetjp_6520_;
}
v_resetjp_6520_:
{
lean_object* v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6526_; 
v___x_6523_ = lean_box(0);
v___x_6524_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_eAssignment_6517_, v_mvarId_6496_, v_val_6497_);
if (v_isShared_6522_ == 0)
{
lean_ctor_set(v___x_6521_, 8, v___x_6524_);
v___x_6526_ = v___x_6521_;
goto v_reusejp_6525_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_depth_6509_);
lean_ctor_set(v_reuseFailAlloc_6532_, 1, v_levelAssignDepth_6510_);
lean_ctor_set(v_reuseFailAlloc_6532_, 2, v_lmvarCounter_6511_);
lean_ctor_set(v_reuseFailAlloc_6532_, 3, v_mvarCounter_6512_);
lean_ctor_set(v_reuseFailAlloc_6532_, 4, v_lDecls_6513_);
lean_ctor_set(v_reuseFailAlloc_6532_, 5, v_decls_6514_);
lean_ctor_set(v_reuseFailAlloc_6532_, 6, v_userNames_6515_);
lean_ctor_set(v_reuseFailAlloc_6532_, 7, v_lAssignment_6516_);
lean_ctor_set(v_reuseFailAlloc_6532_, 8, v___x_6524_);
lean_ctor_set(v_reuseFailAlloc_6532_, 9, v_dAssignment_6518_);
lean_ctor_set(v_reuseFailAlloc_6532_, 10, v_instanceTypedMVars_6519_);
v___x_6526_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6525_;
}
v_reusejp_6525_:
{
lean_object* v___x_6528_; 
if (v_isShared_6508_ == 0)
{
lean_ctor_set(v___x_6507_, 0, v___x_6526_);
v___x_6528_ = v___x_6507_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6531_; 
v_reuseFailAlloc_6531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6531_, 0, v___x_6526_);
lean_ctor_set(v_reuseFailAlloc_6531_, 1, v_cache_6502_);
lean_ctor_set(v_reuseFailAlloc_6531_, 2, v_zetaDeltaFVarIds_6503_);
lean_ctor_set(v_reuseFailAlloc_6531_, 3, v_postponed_6504_);
lean_ctor_set(v_reuseFailAlloc_6531_, 4, v_diag_6505_);
v___x_6528_ = v_reuseFailAlloc_6531_;
goto v_reusejp_6527_;
}
v_reusejp_6527_:
{
lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6529_ = lean_st_ref_put(v___y_6498_, v___x_6528_);
v___x_6530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6530_, 0, v___x_6523_);
return v___x_6530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_mvarId_6535_, lean_object* v_val_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_){
_start:
{
lean_object* v_res_6539_; 
v_res_6539_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6535_, v_val_6536_, v___y_6537_);
lean_dec(v___y_6537_);
return v_res_6539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(lean_object* v_goal_6544_, lean_object* v_c_6545_, lean_object* v_numCases_6546_, uint8_t v_isRec_6547_, lean_object* v_candidates_x3f_6548_, uint8_t v_compress_6549_, lean_object* v_kp_6550_, uint8_t v_stopAtFirstFailure_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_){
_start:
{
lean_object* v___x_6562_; 
v___x_6562_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_6553_);
if (lean_obj_tag(v___x_6562_) == 0)
{
lean_object* v_a_6563_; uint8_t v_trace_6564_; lean_object* v___x_6565_; 
v_a_6563_ = lean_ctor_get(v___x_6562_, 0);
lean_inc(v_a_6563_);
lean_dec_ref_known(v___x_6562_, 1);
v_trace_6564_ = lean_ctor_get_uint8(v_a_6563_, sizeof(void*)*18);
lean_dec(v_a_6563_);
v___x_6565_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v___y_6553_, v___y_6554_, v___y_6558_, v___y_6560_);
if (lean_obj_tag(v___x_6565_) == 0)
{
lean_object* v_a_6566_; lean_object* v___x_6567_; 
v_a_6566_ = lean_ctor_get(v___x_6565_, 0);
lean_inc(v_a_6566_);
lean_dec_ref_known(v___x_6565_, 1);
lean_inc_ref(v_goal_6544_);
v___x_6567_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_6544_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
if (lean_obj_tag(v___x_6567_) == 0)
{
lean_object* v_a_6568_; lean_object* v_mvarId_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___f_6572_; lean_object* v___x_6573_; lean_object* v___f_6574_; lean_object* v___x_6575_; 
v_a_6568_ = lean_ctor_get(v___x_6567_, 0);
lean_inc_n(v_a_6568_, 2);
lean_dec_ref_known(v___x_6567_, 1);
v_mvarId_6569_ = lean_ctor_get(v_goal_6544_, 1);
v___x_6570_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6545_);
v___x_6571_ = lean_box(v_isRec_6547_);
lean_inc_ref_n(v_c_6545_, 2);
lean_inc_ref(v___x_6570_);
v___f_6572_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6572_, 0, v___x_6570_);
lean_closure_set(v___f_6572_, 1, v_c_6545_);
lean_closure_set(v___f_6572_, 2, v_a_6568_);
lean_closure_set(v___f_6572_, 3, v_numCases_6546_);
lean_closure_set(v___f_6572_, 4, v___x_6571_);
v___x_6573_ = lean_box(v_trace_6564_);
lean_inc_ref(v_goal_6544_);
v___f_6574_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_6574_, 0, v_goal_6544_);
lean_closure_set(v___f_6574_, 1, v___x_6573_);
lean_closure_set(v___f_6574_, 2, v___f_6572_);
lean_closure_set(v___f_6574_, 3, v_c_6545_);
lean_closure_set(v___f_6574_, 4, v_candidates_x3f_6548_);
lean_inc(v_mvarId_6569_);
v___x_6575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6569_, v___f_6574_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
if (lean_obj_tag(v___x_6575_) == 0)
{
lean_object* v_a_6576_; lean_object* v___x_6578_; uint8_t v_isShared_6579_; uint8_t v_isSharedCheck_6755_; 
v_a_6576_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6755_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6755_ == 0)
{
v___x_6578_ = v___x_6575_;
v_isShared_6579_ = v_isSharedCheck_6755_;
goto v_resetjp_6577_;
}
else
{
lean_inc(v_a_6576_);
lean_dec(v___x_6575_);
v___x_6578_ = lean_box(0);
v_isShared_6579_ = v_isSharedCheck_6755_;
goto v_resetjp_6577_;
}
v_resetjp_6577_:
{
lean_object* v_fst_6580_; lean_object* v_snd_6581_; lean_object* v___x_6583_; uint8_t v_isShared_6584_; uint8_t v_isSharedCheck_6754_; 
v_fst_6580_ = lean_ctor_get(v_a_6576_, 0);
v_snd_6581_ = lean_ctor_get(v_a_6576_, 1);
v_isSharedCheck_6754_ = !lean_is_exclusive(v_a_6576_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6583_ = v_a_6576_;
v_isShared_6584_ = v_isSharedCheck_6754_;
goto v_resetjp_6582_;
}
else
{
lean_inc(v_snd_6581_);
lean_inc(v_fst_6580_);
lean_dec(v_a_6576_);
v___x_6583_ = lean_box(0);
v_isShared_6584_ = v_isSharedCheck_6754_;
goto v_resetjp_6582_;
}
v_resetjp_6582_:
{
lean_object* v_fst_6585_; lean_object* v_snd_6586_; lean_object* v___x_6588_; uint8_t v_isShared_6589_; uint8_t v_isSharedCheck_6753_; 
v_fst_6585_ = lean_ctor_get(v_fst_6580_, 0);
v_snd_6586_ = lean_ctor_get(v_fst_6580_, 1);
v_isSharedCheck_6753_ = !lean_is_exclusive(v_fst_6580_);
if (v_isSharedCheck_6753_ == 0)
{
v___x_6588_ = v_fst_6580_;
v_isShared_6589_ = v_isSharedCheck_6753_;
goto v_resetjp_6587_;
}
else
{
lean_inc(v_snd_6586_);
lean_inc(v_fst_6585_);
lean_dec(v_fst_6580_);
v___x_6588_ = lean_box(0);
v_isShared_6589_ = v_isSharedCheck_6753_;
goto v_resetjp_6587_;
}
v_resetjp_6587_:
{
lean_object* v___y_6591_; lean_object* v___y_6592_; lean_object* v___y_6593_; lean_object* v___y_6594_; lean_object* v___y_6595_; lean_object* v___f_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v_congrThms_6645_; lean_object* v_simp_6646_; lean_object* v_symSimp_6647_; lean_object* v_symDSimp_6648_; lean_object* v_lastTag_6649_; lean_object* v_counters_6650_; lean_object* v_splitDiags_6651_; lean_object* v_ematchDiags_6652_; lean_object* v_lawfulEqCmpMap_6653_; lean_object* v_reflCmpMap_6654_; lean_object* v_anchors_6655_; lean_object* v_fvarAnchors_6656_; lean_object* v_instanceMap_6657_; lean_object* v_hoistedDecls_6658_; lean_object* v_proofInfos_6659_; lean_object* v_numBranches_6660_; lean_object* v___x_6662_; uint8_t v_isShared_6663_; uint8_t v_isSharedCheck_6752_; 
lean_inc(v_snd_6581_);
v___f_6642_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed), 12, 2);
lean_closure_set(v___f_6642_, 0, v_snd_6581_);
lean_closure_set(v___f_6642_, 1, v_a_6568_);
v___x_6643_ = l_List_lengthTR___redArg(v_fst_6585_);
v___x_6644_ = lean_st_ref_take(v___y_6554_);
v_congrThms_6645_ = lean_ctor_get(v___x_6644_, 0);
v_simp_6646_ = lean_ctor_get(v___x_6644_, 1);
v_symSimp_6647_ = lean_ctor_get(v___x_6644_, 2);
v_symDSimp_6648_ = lean_ctor_get(v___x_6644_, 3);
v_lastTag_6649_ = lean_ctor_get(v___x_6644_, 4);
v_counters_6650_ = lean_ctor_get(v___x_6644_, 5);
v_splitDiags_6651_ = lean_ctor_get(v___x_6644_, 6);
v_ematchDiags_6652_ = lean_ctor_get(v___x_6644_, 7);
v_lawfulEqCmpMap_6653_ = lean_ctor_get(v___x_6644_, 8);
v_reflCmpMap_6654_ = lean_ctor_get(v___x_6644_, 9);
v_anchors_6655_ = lean_ctor_get(v___x_6644_, 10);
v_fvarAnchors_6656_ = lean_ctor_get(v___x_6644_, 11);
v_instanceMap_6657_ = lean_ctor_get(v___x_6644_, 12);
v_hoistedDecls_6658_ = lean_ctor_get(v___x_6644_, 13);
v_proofInfos_6659_ = lean_ctor_get(v___x_6644_, 14);
v_numBranches_6660_ = lean_ctor_get(v___x_6644_, 15);
v_isSharedCheck_6752_ = !lean_is_exclusive(v___x_6644_);
if (v_isSharedCheck_6752_ == 0)
{
v___x_6662_ = v___x_6644_;
v_isShared_6663_ = v_isSharedCheck_6752_;
goto v_resetjp_6661_;
}
else
{
lean_inc(v_numBranches_6660_);
lean_inc(v_proofInfos_6659_);
lean_inc(v_hoistedDecls_6658_);
lean_inc(v_instanceMap_6657_);
lean_inc(v_fvarAnchors_6656_);
lean_inc(v_anchors_6655_);
lean_inc(v_reflCmpMap_6654_);
lean_inc(v_lawfulEqCmpMap_6653_);
lean_inc(v_ematchDiags_6652_);
lean_inc(v_splitDiags_6651_);
lean_inc(v_counters_6650_);
lean_inc(v_lastTag_6649_);
lean_inc(v_symDSimp_6648_);
lean_inc(v_symSimp_6647_);
lean_inc(v_simp_6646_);
lean_inc(v_congrThms_6645_);
lean_dec(v___x_6644_);
v___x_6662_ = lean_box(0);
v_isShared_6663_ = v_isSharedCheck_6752_;
goto v_resetjp_6661_;
}
v___jp_6590_:
{
lean_object* v___x_6596_; uint8_t v___x_6597_; 
v___x_6596_ = lean_array_get_size(v___y_6592_);
v___x_6597_ = lean_nat_dec_eq(v___x_6596_, v___y_6591_);
if (v___x_6597_ == 0)
{
lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6601_; 
lean_dec(v___y_6593_);
lean_dec(v_snd_6586_);
v___x_6598_ = lean_array_to_list(v___y_6592_);
v___x_6599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6599_, 0, v___x_6598_);
if (v_isShared_6579_ == 0)
{
lean_ctor_set(v___x_6578_, 0, v___x_6599_);
v___x_6601_ = v___x_6578_;
goto v_reusejp_6600_;
}
else
{
lean_object* v_reuseFailAlloc_6602_; 
v_reuseFailAlloc_6602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6602_, 0, v___x_6599_);
v___x_6601_ = v_reuseFailAlloc_6602_;
goto v_reusejp_6600_;
}
v_reusejp_6600_:
{
return v___x_6601_;
}
}
else
{
lean_dec(v___y_6592_);
if (lean_obj_tag(v_snd_6586_) == 1)
{
lean_object* v_val_6603_; lean_object* v___x_6605_; uint8_t v_isShared_6606_; uint8_t v_isSharedCheck_6637_; 
lean_del_object(v___x_6578_);
v_val_6603_ = lean_ctor_get(v_snd_6586_, 0);
v_isSharedCheck_6637_ = !lean_is_exclusive(v_snd_6586_);
if (v_isSharedCheck_6637_ == 0)
{
v___x_6605_ = v_snd_6586_;
v_isShared_6606_ = v_isSharedCheck_6637_;
goto v_resetjp_6604_;
}
else
{
lean_inc(v_val_6603_);
lean_dec(v_snd_6586_);
v___x_6605_ = lean_box(0);
v_isShared_6606_ = v_isSharedCheck_6637_;
goto v_resetjp_6604_;
}
v_resetjp_6604_:
{
lean_object* v___x_6607_; 
v___x_6607_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_6603_, v___y_6594_);
lean_dec(v_val_6603_);
if (lean_obj_tag(v___x_6607_) == 0)
{
lean_object* v_a_6608_; lean_object* v___x_6609_; 
v_a_6608_ = lean_ctor_get(v___x_6607_, 0);
lean_inc(v_a_6608_);
lean_dec_ref_known(v___x_6607_, 1);
v___x_6609_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_6608_, v___y_6593_, v_compress_6549_, v___y_6594_, v___y_6595_);
if (lean_obj_tag(v___x_6609_) == 0)
{
lean_object* v_a_6610_; lean_object* v___x_6612_; uint8_t v_isShared_6613_; uint8_t v_isSharedCheck_6620_; 
v_a_6610_ = lean_ctor_get(v___x_6609_, 0);
v_isSharedCheck_6620_ = !lean_is_exclusive(v___x_6609_);
if (v_isSharedCheck_6620_ == 0)
{
v___x_6612_ = v___x_6609_;
v_isShared_6613_ = v_isSharedCheck_6620_;
goto v_resetjp_6611_;
}
else
{
lean_inc(v_a_6610_);
lean_dec(v___x_6609_);
v___x_6612_ = lean_box(0);
v_isShared_6613_ = v_isSharedCheck_6620_;
goto v_resetjp_6611_;
}
v_resetjp_6611_:
{
lean_object* v___x_6615_; 
if (v_isShared_6606_ == 0)
{
lean_ctor_set_tag(v___x_6605_, 0);
lean_ctor_set(v___x_6605_, 0, v_a_6610_);
v___x_6615_ = v___x_6605_;
goto v_reusejp_6614_;
}
else
{
lean_object* v_reuseFailAlloc_6619_; 
v_reuseFailAlloc_6619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6619_, 0, v_a_6610_);
v___x_6615_ = v_reuseFailAlloc_6619_;
goto v_reusejp_6614_;
}
v_reusejp_6614_:
{
lean_object* v___x_6617_; 
if (v_isShared_6613_ == 0)
{
lean_ctor_set(v___x_6612_, 0, v___x_6615_);
v___x_6617_ = v___x_6612_;
goto v_reusejp_6616_;
}
else
{
lean_object* v_reuseFailAlloc_6618_; 
v_reuseFailAlloc_6618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6618_, 0, v___x_6615_);
v___x_6617_ = v_reuseFailAlloc_6618_;
goto v_reusejp_6616_;
}
v_reusejp_6616_:
{
return v___x_6617_;
}
}
}
}
else
{
lean_object* v_a_6621_; lean_object* v___x_6623_; uint8_t v_isShared_6624_; uint8_t v_isSharedCheck_6628_; 
lean_del_object(v___x_6605_);
v_a_6621_ = lean_ctor_get(v___x_6609_, 0);
v_isSharedCheck_6628_ = !lean_is_exclusive(v___x_6609_);
if (v_isSharedCheck_6628_ == 0)
{
v___x_6623_ = v___x_6609_;
v_isShared_6624_ = v_isSharedCheck_6628_;
goto v_resetjp_6622_;
}
else
{
lean_inc(v_a_6621_);
lean_dec(v___x_6609_);
v___x_6623_ = lean_box(0);
v_isShared_6624_ = v_isSharedCheck_6628_;
goto v_resetjp_6622_;
}
v_resetjp_6622_:
{
lean_object* v___x_6626_; 
if (v_isShared_6624_ == 0)
{
v___x_6626_ = v___x_6623_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v_a_6621_);
v___x_6626_ = v_reuseFailAlloc_6627_;
goto v_reusejp_6625_;
}
v_reusejp_6625_:
{
return v___x_6626_;
}
}
}
}
else
{
lean_object* v_a_6629_; lean_object* v___x_6631_; uint8_t v_isShared_6632_; uint8_t v_isSharedCheck_6636_; 
lean_del_object(v___x_6605_);
lean_dec(v___y_6593_);
v_a_6629_ = lean_ctor_get(v___x_6607_, 0);
v_isSharedCheck_6636_ = !lean_is_exclusive(v___x_6607_);
if (v_isSharedCheck_6636_ == 0)
{
v___x_6631_ = v___x_6607_;
v_isShared_6632_ = v_isSharedCheck_6636_;
goto v_resetjp_6630_;
}
else
{
lean_inc(v_a_6629_);
lean_dec(v___x_6607_);
v___x_6631_ = lean_box(0);
v_isShared_6632_ = v_isSharedCheck_6636_;
goto v_resetjp_6630_;
}
v_resetjp_6630_:
{
lean_object* v___x_6634_; 
if (v_isShared_6632_ == 0)
{
v___x_6634_ = v___x_6631_;
goto v_reusejp_6633_;
}
else
{
lean_object* v_reuseFailAlloc_6635_; 
v_reuseFailAlloc_6635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6635_, 0, v_a_6629_);
v___x_6634_ = v_reuseFailAlloc_6635_;
goto v_reusejp_6633_;
}
v_reusejp_6633_:
{
return v___x_6634_;
}
}
}
}
}
else
{
lean_object* v___x_6638_; lean_object* v___x_6640_; 
lean_dec(v___y_6593_);
lean_dec(v_snd_6586_);
v___x_6638_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0));
if (v_isShared_6579_ == 0)
{
lean_ctor_set(v___x_6578_, 0, v___x_6638_);
v___x_6640_ = v___x_6578_;
goto v_reusejp_6639_;
}
else
{
lean_object* v_reuseFailAlloc_6641_; 
v_reuseFailAlloc_6641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6641_, 0, v___x_6638_);
v___x_6640_ = v_reuseFailAlloc_6641_;
goto v_reusejp_6639_;
}
v_reusejp_6639_:
{
return v___x_6640_;
}
}
}
}
v_resetjp_6661_:
{
lean_object* v___y_6665_; 
if (v_isRec_6547_ == 0)
{
lean_object* v___x_6750_; lean_object* v___x_6751_; 
v___x_6750_ = lean_unsigned_to_nat(1u);
v___x_6751_ = lean_nat_sub(v___x_6643_, v___x_6750_);
v___y_6665_ = v___x_6751_;
goto v___jp_6664_;
}
else
{
lean_inc(v___x_6643_);
v___y_6665_ = v___x_6643_;
goto v___jp_6664_;
}
v___jp_6664_:
{
lean_object* v___x_6666_; lean_object* v___x_6668_; 
v___x_6666_ = lean_nat_add(v_numBranches_6660_, v___y_6665_);
lean_dec(v___y_6665_);
lean_dec(v_numBranches_6660_);
if (v_isShared_6663_ == 0)
{
lean_ctor_set(v___x_6662_, 15, v___x_6666_);
v___x_6668_ = v___x_6662_;
goto v_reusejp_6667_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_congrThms_6645_);
lean_ctor_set(v_reuseFailAlloc_6749_, 1, v_simp_6646_);
lean_ctor_set(v_reuseFailAlloc_6749_, 2, v_symSimp_6647_);
lean_ctor_set(v_reuseFailAlloc_6749_, 3, v_symDSimp_6648_);
lean_ctor_set(v_reuseFailAlloc_6749_, 4, v_lastTag_6649_);
lean_ctor_set(v_reuseFailAlloc_6749_, 5, v_counters_6650_);
lean_ctor_set(v_reuseFailAlloc_6749_, 6, v_splitDiags_6651_);
lean_ctor_set(v_reuseFailAlloc_6749_, 7, v_ematchDiags_6652_);
lean_ctor_set(v_reuseFailAlloc_6749_, 8, v_lawfulEqCmpMap_6653_);
lean_ctor_set(v_reuseFailAlloc_6749_, 9, v_reflCmpMap_6654_);
lean_ctor_set(v_reuseFailAlloc_6749_, 10, v_anchors_6655_);
lean_ctor_set(v_reuseFailAlloc_6749_, 11, v_fvarAnchors_6656_);
lean_ctor_set(v_reuseFailAlloc_6749_, 12, v_instanceMap_6657_);
lean_ctor_set(v_reuseFailAlloc_6749_, 13, v_hoistedDecls_6658_);
lean_ctor_set(v_reuseFailAlloc_6749_, 14, v_proofInfos_6659_);
lean_ctor_set(v_reuseFailAlloc_6749_, 15, v___x_6666_);
v___x_6668_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6667_;
}
v_reusejp_6667_:
{
lean_object* v___x_6669_; lean_object* v_toGoalState_6670_; lean_object* v_mvarId_6671_; lean_object* v_goalStack_6672_; lean_object* v___x_6674_; 
v___x_6669_ = lean_st_ref_put(v___y_6554_, v___x_6668_);
v_toGoalState_6670_ = lean_ctor_get(v_snd_6581_, 0);
v_mvarId_6671_ = lean_ctor_get(v_snd_6581_, 1);
lean_inc_n(v_mvarId_6671_, 2);
v_goalStack_6672_ = lean_ctor_get(v_toGoalState_6670_, 18);
lean_inc_ref(v_goalStack_6672_);
lean_inc_ref(v_toGoalState_6670_);
if (v_isShared_6589_ == 0)
{
lean_ctor_set(v___x_6588_, 1, v_toGoalState_6670_);
lean_ctor_set(v___x_6588_, 0, v_mvarId_6671_);
v___x_6674_ = v___x_6588_;
goto v_reusejp_6673_;
}
else
{
lean_object* v_reuseFailAlloc_6748_; 
v_reuseFailAlloc_6748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6748_, 0, v_mvarId_6671_);
lean_ctor_set(v_reuseFailAlloc_6748_, 1, v_toGoalState_6670_);
v___x_6674_ = v_reuseFailAlloc_6748_;
goto v_reusejp_6673_;
}
v_reusejp_6673_:
{
lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; 
lean_inc_ref(v_goalStack_6672_);
v___x_6675_ = lean_array_push(v_goalStack_6672_, v___x_6674_);
lean_inc_ref(v_c_6545_);
v___x_6676_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_6676_, 0, v_c_6545_);
lean_inc(v_mvarId_6671_);
v___x_6677_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6671_, v___x_6676_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
if (lean_obj_tag(v___x_6677_) == 0)
{
lean_object* v_a_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; uint64_t v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6687_; 
v_a_6678_ = lean_ctor_get(v___x_6677_, 0);
lean_inc(v_a_6678_);
lean_dec_ref_known(v___x_6677_, 1);
v___x_6679_ = lean_unsigned_to_nat(0u);
v___x_6680_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1));
v___x_6681_ = lean_unbox_uint64(v_a_6678_);
lean_dec(v_a_6678_);
lean_inc_n(v___x_6643_, 2);
lean_inc_ref(v_toGoalState_6670_);
v___x_6682_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_toGoalState_6670_, v_c_6545_, v___x_6570_, v___x_6643_, v___x_6675_, v___x_6681_, v_fst_6585_, v___x_6680_);
lean_dec_ref(v_c_6545_);
v___x_6683_ = lean_box(0);
v___x_6684_ = lean_unsigned_to_nat(1u);
v___x_6685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6685_, 0, v___x_6679_);
lean_ctor_set(v___x_6685_, 1, v___x_6643_);
lean_ctor_set(v___x_6685_, 2, v___x_6684_);
if (v_isShared_6584_ == 0)
{
lean_ctor_set(v___x_6583_, 1, v___x_6685_);
lean_ctor_set(v___x_6583_, 0, v___x_6683_);
v___x_6687_ = v___x_6583_;
goto v_reusejp_6686_;
}
else
{
lean_object* v_reuseFailAlloc_6739_; 
v_reuseFailAlloc_6739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6739_, 0, v___x_6683_);
lean_ctor_set(v_reuseFailAlloc_6739_, 1, v___x_6685_);
v___x_6687_ = v_reuseFailAlloc_6739_;
goto v_reusejp_6686_;
}
v_reusejp_6686_:
{
lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; 
v___x_6688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6688_, 0, v___x_6680_);
lean_ctor_set(v___x_6688_, 1, v___x_6687_);
v___x_6689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6689_, 0, v___x_6680_);
lean_ctor_set(v___x_6689_, 1, v___x_6688_);
v___x_6690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6690_, 0, v___x_6683_);
lean_ctor_set(v___x_6690_, 1, v___x_6689_);
lean_inc(v_mvarId_6671_);
v___x_6691_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6550_, v_a_6566_, v_goal_6544_, v___x_6643_, v_snd_6581_, v_mvarId_6671_, v_stopAtFirstFailure_6551_, v_goalStack_6672_, v___x_6682_, v___x_6690_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
lean_dec(v___x_6682_);
lean_dec_ref(v_goalStack_6672_);
lean_dec(v___x_6643_);
if (lean_obj_tag(v___x_6691_) == 0)
{
lean_object* v_a_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6730_; 
v_a_6692_ = lean_ctor_get(v___x_6691_, 0);
v_isSharedCheck_6730_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6730_ == 0)
{
v___x_6694_ = v___x_6691_;
v_isShared_6695_ = v_isSharedCheck_6730_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_a_6692_);
lean_dec(v___x_6691_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6730_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v_fst_6696_; 
v_fst_6696_ = lean_ctor_get(v_a_6692_, 0);
if (lean_obj_tag(v_fst_6696_) == 0)
{
lean_object* v_snd_6697_; lean_object* v_snd_6698_; lean_object* v_fst_6699_; lean_object* v_fst_6700_; lean_object* v___x_6701_; 
lean_del_object(v___x_6694_);
v_snd_6697_ = lean_ctor_get(v_a_6692_, 1);
lean_inc(v_snd_6697_);
lean_dec(v_a_6692_);
v_snd_6698_ = lean_ctor_get(v_snd_6697_, 1);
lean_inc(v_snd_6698_);
v_fst_6699_ = lean_ctor_get(v_snd_6697_, 0);
lean_inc(v_fst_6699_);
lean_dec(v_snd_6697_);
v_fst_6700_ = lean_ctor_get(v_snd_6698_, 0);
lean_inc(v_fst_6700_);
lean_dec(v_snd_6698_);
lean_inc(v_mvarId_6671_);
v___x_6701_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6671_, v___f_6642_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
if (lean_obj_tag(v___x_6701_) == 0)
{
lean_object* v_a_6702_; lean_object* v___x_6703_; 
v_a_6702_ = lean_ctor_get(v___x_6701_, 0);
lean_inc(v_a_6702_);
lean_dec_ref_known(v___x_6701_, 1);
lean_inc(v_mvarId_6671_);
v___x_6703_ = l_Lean_MVarId_getType(v_mvarId_6671_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
if (lean_obj_tag(v___x_6703_) == 0)
{
lean_object* v_a_6704_; uint8_t v___x_6705_; 
v_a_6704_ = lean_ctor_get(v___x_6703_, 0);
lean_inc(v_a_6704_);
lean_dec_ref_known(v___x_6703_, 1);
v___x_6705_ = l_Lean_Expr_isFalse(v_a_6704_);
lean_dec(v_a_6704_);
if (v___x_6705_ == 0)
{
lean_object* v___x_6706_; 
v___x_6706_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6671_, v_a_6702_, v___y_6558_);
lean_dec_ref(v___x_6706_);
v___y_6591_ = v___x_6679_;
v___y_6592_ = v_fst_6700_;
v___y_6593_ = v_fst_6699_;
v___y_6594_ = v___y_6559_;
v___y_6595_ = v___y_6560_;
goto v___jp_6590_;
}
else
{
lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; 
v___x_6707_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_6708_ = l_Lean_Meta_mkExpectedPropHint(v_a_6702_, v___x_6707_);
v___x_6709_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6671_, v___x_6708_, v___y_6558_);
lean_dec_ref(v___x_6709_);
v___y_6591_ = v___x_6679_;
v___y_6592_ = v_fst_6700_;
v___y_6593_ = v_fst_6699_;
v___y_6594_ = v___y_6559_;
v___y_6595_ = v___y_6560_;
goto v___jp_6590_;
}
}
else
{
lean_object* v_a_6710_; lean_object* v___x_6712_; uint8_t v_isShared_6713_; uint8_t v_isSharedCheck_6717_; 
lean_dec(v_a_6702_);
lean_dec(v_fst_6700_);
lean_dec(v_fst_6699_);
lean_dec(v_mvarId_6671_);
lean_dec(v_snd_6586_);
lean_del_object(v___x_6578_);
v_a_6710_ = lean_ctor_get(v___x_6703_, 0);
v_isSharedCheck_6717_ = !lean_is_exclusive(v___x_6703_);
if (v_isSharedCheck_6717_ == 0)
{
v___x_6712_ = v___x_6703_;
v_isShared_6713_ = v_isSharedCheck_6717_;
goto v_resetjp_6711_;
}
else
{
lean_inc(v_a_6710_);
lean_dec(v___x_6703_);
v___x_6712_ = lean_box(0);
v_isShared_6713_ = v_isSharedCheck_6717_;
goto v_resetjp_6711_;
}
v_resetjp_6711_:
{
lean_object* v___x_6715_; 
if (v_isShared_6713_ == 0)
{
v___x_6715_ = v___x_6712_;
goto v_reusejp_6714_;
}
else
{
lean_object* v_reuseFailAlloc_6716_; 
v_reuseFailAlloc_6716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_a_6710_);
v___x_6715_ = v_reuseFailAlloc_6716_;
goto v_reusejp_6714_;
}
v_reusejp_6714_:
{
return v___x_6715_;
}
}
}
}
else
{
lean_object* v_a_6718_; lean_object* v___x_6720_; uint8_t v_isShared_6721_; uint8_t v_isSharedCheck_6725_; 
lean_dec(v_fst_6700_);
lean_dec(v_fst_6699_);
lean_dec(v_mvarId_6671_);
lean_dec(v_snd_6586_);
lean_del_object(v___x_6578_);
v_a_6718_ = lean_ctor_get(v___x_6701_, 0);
v_isSharedCheck_6725_ = !lean_is_exclusive(v___x_6701_);
if (v_isSharedCheck_6725_ == 0)
{
v___x_6720_ = v___x_6701_;
v_isShared_6721_ = v_isSharedCheck_6725_;
goto v_resetjp_6719_;
}
else
{
lean_inc(v_a_6718_);
lean_dec(v___x_6701_);
v___x_6720_ = lean_box(0);
v_isShared_6721_ = v_isSharedCheck_6725_;
goto v_resetjp_6719_;
}
v_resetjp_6719_:
{
lean_object* v___x_6723_; 
if (v_isShared_6721_ == 0)
{
v___x_6723_ = v___x_6720_;
goto v_reusejp_6722_;
}
else
{
lean_object* v_reuseFailAlloc_6724_; 
v_reuseFailAlloc_6724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_a_6718_);
v___x_6723_ = v_reuseFailAlloc_6724_;
goto v_reusejp_6722_;
}
v_reusejp_6722_:
{
return v___x_6723_;
}
}
}
}
else
{
lean_object* v_val_6726_; lean_object* v___x_6728_; 
lean_inc_ref(v_fst_6696_);
lean_dec(v_a_6692_);
lean_dec(v_mvarId_6671_);
lean_dec_ref(v___f_6642_);
lean_dec(v_snd_6586_);
lean_del_object(v___x_6578_);
v_val_6726_ = lean_ctor_get(v_fst_6696_, 0);
lean_inc(v_val_6726_);
lean_dec_ref_known(v_fst_6696_, 1);
if (v_isShared_6695_ == 0)
{
lean_ctor_set(v___x_6694_, 0, v_val_6726_);
v___x_6728_ = v___x_6694_;
goto v_reusejp_6727_;
}
else
{
lean_object* v_reuseFailAlloc_6729_; 
v_reuseFailAlloc_6729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6729_, 0, v_val_6726_);
v___x_6728_ = v_reuseFailAlloc_6729_;
goto v_reusejp_6727_;
}
v_reusejp_6727_:
{
return v___x_6728_;
}
}
}
}
else
{
lean_object* v_a_6731_; lean_object* v___x_6733_; uint8_t v_isShared_6734_; uint8_t v_isSharedCheck_6738_; 
lean_dec(v_mvarId_6671_);
lean_dec_ref(v___f_6642_);
lean_dec(v_snd_6586_);
lean_del_object(v___x_6578_);
v_a_6731_ = lean_ctor_get(v___x_6691_, 0);
v_isSharedCheck_6738_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6738_ == 0)
{
v___x_6733_ = v___x_6691_;
v_isShared_6734_ = v_isSharedCheck_6738_;
goto v_resetjp_6732_;
}
else
{
lean_inc(v_a_6731_);
lean_dec(v___x_6691_);
v___x_6733_ = lean_box(0);
v_isShared_6734_ = v_isSharedCheck_6738_;
goto v_resetjp_6732_;
}
v_resetjp_6732_:
{
lean_object* v___x_6736_; 
if (v_isShared_6734_ == 0)
{
v___x_6736_ = v___x_6733_;
goto v_reusejp_6735_;
}
else
{
lean_object* v_reuseFailAlloc_6737_; 
v_reuseFailAlloc_6737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6737_, 0, v_a_6731_);
v___x_6736_ = v_reuseFailAlloc_6737_;
goto v_reusejp_6735_;
}
v_reusejp_6735_:
{
return v___x_6736_;
}
}
}
}
}
else
{
lean_object* v_a_6740_; lean_object* v___x_6742_; uint8_t v_isShared_6743_; uint8_t v_isSharedCheck_6747_; 
lean_dec_ref(v___x_6675_);
lean_dec_ref(v_goalStack_6672_);
lean_dec(v_mvarId_6671_);
lean_dec(v___x_6643_);
lean_dec_ref(v___f_6642_);
lean_dec(v_snd_6586_);
lean_dec(v_fst_6585_);
lean_del_object(v___x_6583_);
lean_dec(v_snd_6581_);
lean_del_object(v___x_6578_);
lean_dec_ref(v___x_6570_);
lean_dec(v_a_6566_);
lean_dec_ref(v_kp_6550_);
lean_dec_ref(v_c_6545_);
lean_dec_ref(v_goal_6544_);
v_a_6740_ = lean_ctor_get(v___x_6677_, 0);
v_isSharedCheck_6747_ = !lean_is_exclusive(v___x_6677_);
if (v_isSharedCheck_6747_ == 0)
{
v___x_6742_ = v___x_6677_;
v_isShared_6743_ = v_isSharedCheck_6747_;
goto v_resetjp_6741_;
}
else
{
lean_inc(v_a_6740_);
lean_dec(v___x_6677_);
v___x_6742_ = lean_box(0);
v_isShared_6743_ = v_isSharedCheck_6747_;
goto v_resetjp_6741_;
}
v_resetjp_6741_:
{
lean_object* v___x_6745_; 
if (v_isShared_6743_ == 0)
{
v___x_6745_ = v___x_6742_;
goto v_reusejp_6744_;
}
else
{
lean_object* v_reuseFailAlloc_6746_; 
v_reuseFailAlloc_6746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6746_, 0, v_a_6740_);
v___x_6745_ = v_reuseFailAlloc_6746_;
goto v_reusejp_6744_;
}
v_reusejp_6744_:
{
return v___x_6745_;
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
}
else
{
lean_object* v_a_6756_; lean_object* v___x_6758_; uint8_t v_isShared_6759_; uint8_t v_isSharedCheck_6763_; 
lean_dec_ref(v___x_6570_);
lean_dec(v_a_6568_);
lean_dec(v_a_6566_);
lean_dec_ref(v_kp_6550_);
lean_dec_ref(v_c_6545_);
lean_dec_ref(v_goal_6544_);
v_a_6756_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6763_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6763_ == 0)
{
v___x_6758_ = v___x_6575_;
v_isShared_6759_ = v_isSharedCheck_6763_;
goto v_resetjp_6757_;
}
else
{
lean_inc(v_a_6756_);
lean_dec(v___x_6575_);
v___x_6758_ = lean_box(0);
v_isShared_6759_ = v_isSharedCheck_6763_;
goto v_resetjp_6757_;
}
v_resetjp_6757_:
{
lean_object* v___x_6761_; 
if (v_isShared_6759_ == 0)
{
v___x_6761_ = v___x_6758_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6762_; 
v_reuseFailAlloc_6762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6762_, 0, v_a_6756_);
v___x_6761_ = v_reuseFailAlloc_6762_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
return v___x_6761_;
}
}
}
}
else
{
lean_object* v_a_6764_; lean_object* v___x_6766_; uint8_t v_isShared_6767_; uint8_t v_isSharedCheck_6771_; 
lean_dec(v_a_6566_);
lean_dec_ref(v_kp_6550_);
lean_dec(v_candidates_x3f_6548_);
lean_dec(v_numCases_6546_);
lean_dec_ref(v_c_6545_);
lean_dec_ref(v_goal_6544_);
v_a_6764_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6771_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6771_ == 0)
{
v___x_6766_ = v___x_6567_;
v_isShared_6767_ = v_isSharedCheck_6771_;
goto v_resetjp_6765_;
}
else
{
lean_inc(v_a_6764_);
lean_dec(v___x_6567_);
v___x_6766_ = lean_box(0);
v_isShared_6767_ = v_isSharedCheck_6771_;
goto v_resetjp_6765_;
}
v_resetjp_6765_:
{
lean_object* v___x_6769_; 
if (v_isShared_6767_ == 0)
{
v___x_6769_ = v___x_6766_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6770_; 
v_reuseFailAlloc_6770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6770_, 0, v_a_6764_);
v___x_6769_ = v_reuseFailAlloc_6770_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
return v___x_6769_;
}
}
}
}
else
{
lean_object* v_a_6772_; lean_object* v___x_6774_; uint8_t v_isShared_6775_; uint8_t v_isSharedCheck_6779_; 
lean_dec_ref(v_kp_6550_);
lean_dec(v_candidates_x3f_6548_);
lean_dec(v_numCases_6546_);
lean_dec_ref(v_c_6545_);
lean_dec_ref(v_goal_6544_);
v_a_6772_ = lean_ctor_get(v___x_6565_, 0);
v_isSharedCheck_6779_ = !lean_is_exclusive(v___x_6565_);
if (v_isSharedCheck_6779_ == 0)
{
v___x_6774_ = v___x_6565_;
v_isShared_6775_ = v_isSharedCheck_6779_;
goto v_resetjp_6773_;
}
else
{
lean_inc(v_a_6772_);
lean_dec(v___x_6565_);
v___x_6774_ = lean_box(0);
v_isShared_6775_ = v_isSharedCheck_6779_;
goto v_resetjp_6773_;
}
v_resetjp_6773_:
{
lean_object* v___x_6777_; 
if (v_isShared_6775_ == 0)
{
v___x_6777_ = v___x_6774_;
goto v_reusejp_6776_;
}
else
{
lean_object* v_reuseFailAlloc_6778_; 
v_reuseFailAlloc_6778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6772_);
v___x_6777_ = v_reuseFailAlloc_6778_;
goto v_reusejp_6776_;
}
v_reusejp_6776_:
{
return v___x_6777_;
}
}
}
}
else
{
lean_object* v_a_6780_; lean_object* v___x_6782_; uint8_t v_isShared_6783_; uint8_t v_isSharedCheck_6787_; 
lean_dec_ref(v_kp_6550_);
lean_dec(v_candidates_x3f_6548_);
lean_dec(v_numCases_6546_);
lean_dec_ref(v_c_6545_);
lean_dec_ref(v_goal_6544_);
v_a_6780_ = lean_ctor_get(v___x_6562_, 0);
v_isSharedCheck_6787_ = !lean_is_exclusive(v___x_6562_);
if (v_isSharedCheck_6787_ == 0)
{
v___x_6782_ = v___x_6562_;
v_isShared_6783_ = v_isSharedCheck_6787_;
goto v_resetjp_6781_;
}
else
{
lean_inc(v_a_6780_);
lean_dec(v___x_6562_);
v___x_6782_ = lean_box(0);
v_isShared_6783_ = v_isSharedCheck_6787_;
goto v_resetjp_6781_;
}
v_resetjp_6781_:
{
lean_object* v___x_6785_; 
if (v_isShared_6783_ == 0)
{
v___x_6785_ = v___x_6782_;
goto v_reusejp_6784_;
}
else
{
lean_object* v_reuseFailAlloc_6786_; 
v_reuseFailAlloc_6786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6786_, 0, v_a_6780_);
v___x_6785_ = v_reuseFailAlloc_6786_;
goto v_reusejp_6784_;
}
v_reusejp_6784_:
{
return v___x_6785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_goal_6788_ = _args[0];
lean_object* v_c_6789_ = _args[1];
lean_object* v_numCases_6790_ = _args[2];
lean_object* v_isRec_6791_ = _args[3];
lean_object* v_candidates_x3f_6792_ = _args[4];
lean_object* v_compress_6793_ = _args[5];
lean_object* v_kp_6794_ = _args[6];
lean_object* v_stopAtFirstFailure_6795_ = _args[7];
lean_object* v___y_6796_ = _args[8];
lean_object* v___y_6797_ = _args[9];
lean_object* v___y_6798_ = _args[10];
lean_object* v___y_6799_ = _args[11];
lean_object* v___y_6800_ = _args[12];
lean_object* v___y_6801_ = _args[13];
lean_object* v___y_6802_ = _args[14];
lean_object* v___y_6803_ = _args[15];
lean_object* v___y_6804_ = _args[16];
lean_object* v___y_6805_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6806_; uint8_t v_compress_boxed_6807_; uint8_t v_stopAtFirstFailure_boxed_6808_; lean_object* v_res_6809_; 
v_isRec_boxed_6806_ = lean_unbox(v_isRec_6791_);
v_compress_boxed_6807_ = lean_unbox(v_compress_6793_);
v_stopAtFirstFailure_boxed_6808_ = lean_unbox(v_stopAtFirstFailure_6795_);
v_res_6809_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(v_goal_6788_, v_c_6789_, v_numCases_6790_, v_isRec_boxed_6806_, v_candidates_x3f_6792_, v_compress_boxed_6807_, v_kp_6794_, v_stopAtFirstFailure_boxed_6808_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_);
lean_dec(v___y_6804_);
lean_dec_ref(v___y_6803_);
lean_dec(v___y_6802_);
lean_dec_ref(v___y_6801_);
lean_dec(v___y_6800_);
lean_dec_ref(v___y_6799_);
lean_dec(v___y_6798_);
lean_dec_ref(v___y_6797_);
lean_dec(v___y_6796_);
return v_res_6809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_6810_, lean_object* v_numCases_6811_, uint8_t v_isRec_6812_, uint8_t v_stopAtFirstFailure_6813_, uint8_t v_compress_6814_, lean_object* v_candidates_x3f_6815_, lean_object* v_goal_6816_, lean_object* v_kp_6817_, lean_object* v_a_6818_, lean_object* v_a_6819_, lean_object* v_a_6820_, lean_object* v_a_6821_, lean_object* v_a_6822_, lean_object* v_a_6823_, lean_object* v_a_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_){
_start:
{
lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; lean_object* v___f_6831_; lean_object* v___x_6832_; 
v___x_6828_ = lean_box(v_isRec_6812_);
v___x_6829_ = lean_box(v_compress_6814_);
v___x_6830_ = lean_box(v_stopAtFirstFailure_6813_);
lean_inc_ref(v_goal_6816_);
v___f_6831_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed), 18, 8);
lean_closure_set(v___f_6831_, 0, v_goal_6816_);
lean_closure_set(v___f_6831_, 1, v_c_6810_);
lean_closure_set(v___f_6831_, 2, v_numCases_6811_);
lean_closure_set(v___f_6831_, 3, v___x_6828_);
lean_closure_set(v___f_6831_, 4, v_candidates_x3f_6815_);
lean_closure_set(v___f_6831_, 5, v___x_6829_);
lean_closure_set(v___f_6831_, 6, v_kp_6817_);
lean_closure_set(v___f_6831_, 7, v___x_6830_);
v___x_6832_ = l_Lean_Meta_Grind_withHoistedDecls___redArg(v_goal_6816_, v___f_6831_, v_a_6818_, v_a_6819_, v_a_6820_, v_a_6821_, v_a_6822_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
return v___x_6832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6833_ = _args[0];
lean_object* v_numCases_6834_ = _args[1];
lean_object* v_isRec_6835_ = _args[2];
lean_object* v_stopAtFirstFailure_6836_ = _args[3];
lean_object* v_compress_6837_ = _args[4];
lean_object* v_candidates_x3f_6838_ = _args[5];
lean_object* v_goal_6839_ = _args[6];
lean_object* v_kp_6840_ = _args[7];
lean_object* v_a_6841_ = _args[8];
lean_object* v_a_6842_ = _args[9];
lean_object* v_a_6843_ = _args[10];
lean_object* v_a_6844_ = _args[11];
lean_object* v_a_6845_ = _args[12];
lean_object* v_a_6846_ = _args[13];
lean_object* v_a_6847_ = _args[14];
lean_object* v_a_6848_ = _args[15];
lean_object* v_a_6849_ = _args[16];
lean_object* v_a_6850_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6851_; uint8_t v_stopAtFirstFailure_boxed_6852_; uint8_t v_compress_boxed_6853_; lean_object* v_res_6854_; 
v_isRec_boxed_6851_ = lean_unbox(v_isRec_6835_);
v_stopAtFirstFailure_boxed_6852_ = lean_unbox(v_stopAtFirstFailure_6836_);
v_compress_boxed_6853_ = lean_unbox(v_compress_6837_);
v_res_6854_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6833_, v_numCases_6834_, v_isRec_boxed_6851_, v_stopAtFirstFailure_boxed_6852_, v_compress_boxed_6853_, v_candidates_x3f_6838_, v_goal_6839_, v_kp_6840_, v_a_6841_, v_a_6842_, v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_, v_a_6847_, v_a_6848_, v_a_6849_);
lean_dec(v_a_6849_);
lean_dec_ref(v_a_6848_);
lean_dec(v_a_6847_);
lean_dec_ref(v_a_6846_);
lean_dec(v_a_6845_);
lean_dec_ref(v_a_6844_);
lean_dec(v_a_6843_);
lean_dec_ref(v_a_6842_);
lean_dec(v_a_6841_);
return v_res_6854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6855_, lean_object* v_numCases_6856_, uint8_t v_isRec_6857_, uint8_t v_stopAtFirstFailure_6858_, uint8_t v_compress_6859_, lean_object* v_candidates_x3f_6860_, lean_object* v_goal_6861_, lean_object* v_x_6862_, lean_object* v_kp_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_){
_start:
{
lean_object* v___x_6874_; 
v___x_6874_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6855_, v_numCases_6856_, v_isRec_6857_, v_stopAtFirstFailure_6858_, v_compress_6859_, v_candidates_x3f_6860_, v_goal_6861_, v_kp_6863_, v_a_6864_, v_a_6865_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_, v_a_6872_);
return v___x_6874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6875_ = _args[0];
lean_object* v_numCases_6876_ = _args[1];
lean_object* v_isRec_6877_ = _args[2];
lean_object* v_stopAtFirstFailure_6878_ = _args[3];
lean_object* v_compress_6879_ = _args[4];
lean_object* v_candidates_x3f_6880_ = _args[5];
lean_object* v_goal_6881_ = _args[6];
lean_object* v_x_6882_ = _args[7];
lean_object* v_kp_6883_ = _args[8];
lean_object* v_a_6884_ = _args[9];
lean_object* v_a_6885_ = _args[10];
lean_object* v_a_6886_ = _args[11];
lean_object* v_a_6887_ = _args[12];
lean_object* v_a_6888_ = _args[13];
lean_object* v_a_6889_ = _args[14];
lean_object* v_a_6890_ = _args[15];
lean_object* v_a_6891_ = _args[16];
lean_object* v_a_6892_ = _args[17];
lean_object* v_a_6893_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6894_; uint8_t v_stopAtFirstFailure_boxed_6895_; uint8_t v_compress_boxed_6896_; lean_object* v_res_6897_; 
v_isRec_boxed_6894_ = lean_unbox(v_isRec_6877_);
v_stopAtFirstFailure_boxed_6895_ = lean_unbox(v_stopAtFirstFailure_6878_);
v_compress_boxed_6896_ = lean_unbox(v_compress_6879_);
v_res_6897_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6875_, v_numCases_6876_, v_isRec_boxed_6894_, v_stopAtFirstFailure_boxed_6895_, v_compress_boxed_6896_, v_candidates_x3f_6880_, v_goal_6881_, v_x_6882_, v_kp_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_, v_a_6891_, v_a_6892_);
lean_dec(v_a_6892_);
lean_dec_ref(v_a_6891_);
lean_dec(v_a_6890_);
lean_dec_ref(v_a_6889_);
lean_dec(v_a_6888_);
lean_dec_ref(v_a_6887_);
lean_dec(v_a_6886_);
lean_dec_ref(v_a_6885_);
lean_dec(v_a_6884_);
lean_dec_ref(v_x_6882_);
return v_res_6897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_6898_, lean_object* v_a_6899_, lean_object* v_goal_6900_, lean_object* v___x_6901_, lean_object* v_snd_6902_, lean_object* v___x_6903_, uint8_t v_stopAtFirstFailure_6904_, lean_object* v___x_6905_, lean_object* v_as_6906_, lean_object* v_as_x27_6907_, lean_object* v_b_6908_, lean_object* v_a_6909_, lean_object* v___y_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_){
_start:
{
lean_object* v___x_6920_; 
v___x_6920_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6898_, v_a_6899_, v_goal_6900_, v___x_6901_, v_snd_6902_, v___x_6903_, v_stopAtFirstFailure_6904_, v___x_6905_, v_as_x27_6907_, v_b_6908_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_);
return v___x_6920_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6921_ = _args[0];
lean_object* v_a_6922_ = _args[1];
lean_object* v_goal_6923_ = _args[2];
lean_object* v___x_6924_ = _args[3];
lean_object* v_snd_6925_ = _args[4];
lean_object* v___x_6926_ = _args[5];
lean_object* v_stopAtFirstFailure_6927_ = _args[6];
lean_object* v___x_6928_ = _args[7];
lean_object* v_as_6929_ = _args[8];
lean_object* v_as_x27_6930_ = _args[9];
lean_object* v_b_6931_ = _args[10];
lean_object* v_a_6932_ = _args[11];
lean_object* v___y_6933_ = _args[12];
lean_object* v___y_6934_ = _args[13];
lean_object* v___y_6935_ = _args[14];
lean_object* v___y_6936_ = _args[15];
lean_object* v___y_6937_ = _args[16];
lean_object* v___y_6938_ = _args[17];
lean_object* v___y_6939_ = _args[18];
lean_object* v___y_6940_ = _args[19];
lean_object* v___y_6941_ = _args[20];
lean_object* v___y_6942_ = _args[21];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6943_; lean_object* v_res_6944_; 
v_stopAtFirstFailure_boxed_6943_ = lean_unbox(v_stopAtFirstFailure_6927_);
v_res_6944_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6921_, v_a_6922_, v_goal_6923_, v___x_6924_, v_snd_6925_, v___x_6926_, v_stopAtFirstFailure_boxed_6943_, v___x_6928_, v_as_6929_, v_as_x27_6930_, v_b_6931_, v_a_6932_, v___y_6933_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_);
lean_dec(v___y_6941_);
lean_dec_ref(v___y_6940_);
lean_dec(v___y_6939_);
lean_dec_ref(v___y_6938_);
lean_dec(v___y_6937_);
lean_dec_ref(v___y_6936_);
lean_dec(v___y_6935_);
lean_dec_ref(v___y_6934_);
lean_dec(v___y_6933_);
lean_dec(v_as_x27_6930_);
lean_dec(v_as_6929_);
lean_dec_ref(v___x_6928_);
lean_dec(v___x_6924_);
return v_res_6944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_mvarId_6945_, lean_object* v_val_6946_, lean_object* v___y_6947_, lean_object* v___y_6948_, lean_object* v___y_6949_, lean_object* v___y_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
lean_object* v___x_6957_; 
v___x_6957_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6945_, v_val_6946_, v___y_6953_);
return v___x_6957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_mvarId_6958_, lean_object* v_val_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_){
_start:
{
lean_object* v_res_6970_; 
v_res_6970_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_mvarId_6958_, v_val_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_);
lean_dec(v___y_6968_);
lean_dec_ref(v___y_6967_);
lean_dec(v___y_6966_);
lean_dec_ref(v___y_6965_);
lean_dec(v___y_6964_);
lean_dec_ref(v___y_6963_);
lean_dec(v___y_6962_);
lean_dec_ref(v___y_6961_);
lean_dec(v___y_6960_);
return v_res_6970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4(lean_object* v_00_u03b2_6971_, lean_object* v_x_6972_, lean_object* v_x_6973_, lean_object* v_x_6974_){
_start:
{
lean_object* v___x_6975_; 
v___x_6975_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_x_6972_, v_x_6973_, v_x_6974_);
return v___x_6975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(lean_object* v_00_u03b2_6976_, lean_object* v_x_6977_, size_t v_x_6978_, size_t v_x_6979_, lean_object* v_x_6980_, lean_object* v_x_6981_){
_start:
{
lean_object* v___x_6982_; 
v___x_6982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6977_, v_x_6978_, v_x_6979_, v_x_6980_, v_x_6981_);
return v___x_6982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b2_6983_, lean_object* v_x_6984_, lean_object* v_x_6985_, lean_object* v_x_6986_, lean_object* v_x_6987_, lean_object* v_x_6988_){
_start:
{
size_t v_x_118980__boxed_6989_; size_t v_x_118981__boxed_6990_; lean_object* v_res_6991_; 
v_x_118980__boxed_6989_ = lean_unbox_usize(v_x_6985_);
lean_dec(v_x_6985_);
v_x_118981__boxed_6990_ = lean_unbox_usize(v_x_6986_);
lean_dec(v_x_6986_);
v_res_6991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(v_00_u03b2_6983_, v_x_6984_, v_x_118980__boxed_6989_, v_x_118981__boxed_6990_, v_x_6987_, v_x_6988_);
return v_res_6991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_6992_, lean_object* v_n_6993_, lean_object* v_k_6994_, lean_object* v_v_6995_){
_start:
{
lean_object* v___x_6996_; 
v___x_6996_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v_n_6993_, v_k_6994_, v_v_6995_);
return v___x_6996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_6997_, size_t v_depth_6998_, lean_object* v_keys_6999_, lean_object* v_vals_7000_, lean_object* v_heq_7001_, lean_object* v_i_7002_, lean_object* v_entries_7003_){
_start:
{
lean_object* v___x_7004_; 
v___x_7004_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_6998_, v_keys_6999_, v_vals_7000_, v_i_7002_, v_entries_7003_);
return v___x_7004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_7005_, lean_object* v_depth_7006_, lean_object* v_keys_7007_, lean_object* v_vals_7008_, lean_object* v_heq_7009_, lean_object* v_i_7010_, lean_object* v_entries_7011_){
_start:
{
size_t v_depth_boxed_7012_; lean_object* v_res_7013_; 
v_depth_boxed_7012_ = lean_unbox_usize(v_depth_7006_);
lean_dec(v_depth_7006_);
v_res_7013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(v_00_u03b2_7005_, v_depth_boxed_7012_, v_keys_7007_, v_vals_7008_, v_heq_7009_, v_i_7010_, v_entries_7011_);
lean_dec_ref(v_vals_7008_);
lean_dec_ref(v_keys_7007_);
return v_res_7013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_7014_, lean_object* v_x_7015_, lean_object* v_x_7016_, lean_object* v_x_7017_, lean_object* v_x_7018_){
_start:
{
lean_object* v___x_7019_; 
v___x_7019_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_x_7015_, v_x_7016_, v_x_7017_, v_x_7018_);
return v___x_7019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_, lean_object* v___y_7026_, lean_object* v___y_7027_, lean_object* v___y_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_){
_start:
{
lean_object* v___x_7033_; 
v___x_7033_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_7020_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_);
return v___x_7033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_, lean_object* v___y_7042_, lean_object* v___y_7043_, lean_object* v___y_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_){
_start:
{
lean_object* v_res_7047_; 
v_res_7047_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_, v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
lean_dec(v___y_7045_);
lean_dec_ref(v___y_7044_);
lean_dec(v___y_7043_);
lean_dec_ref(v___y_7042_);
lean_dec(v___y_7041_);
lean_dec_ref(v___y_7040_);
lean_dec(v___y_7039_);
lean_dec_ref(v___y_7038_);
lean_dec(v___y_7037_);
lean_dec_ref(v___y_7035_);
return v_res_7047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_){
_start:
{
lean_object* v___x_7059_; lean_object* v___x_7060_; 
v___x_7059_ = lean_st_mk_ref(v_goal_7048_);
v___x_7060_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_7059_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_, v___y_7057_);
if (lean_obj_tag(v___x_7060_) == 0)
{
lean_object* v_a_7061_; lean_object* v___x_7063_; uint8_t v_isShared_7064_; uint8_t v_isSharedCheck_7070_; 
v_a_7061_ = lean_ctor_get(v___x_7060_, 0);
v_isSharedCheck_7070_ = !lean_is_exclusive(v___x_7060_);
if (v_isSharedCheck_7070_ == 0)
{
v___x_7063_ = v___x_7060_;
v_isShared_7064_ = v_isSharedCheck_7070_;
goto v_resetjp_7062_;
}
else
{
lean_inc(v_a_7061_);
lean_dec(v___x_7060_);
v___x_7063_ = lean_box(0);
v_isShared_7064_ = v_isSharedCheck_7070_;
goto v_resetjp_7062_;
}
v_resetjp_7062_:
{
lean_object* v___x_7065_; lean_object* v___x_7066_; lean_object* v___x_7068_; 
v___x_7065_ = lean_st_ref_get(v___x_7059_);
lean_dec(v___x_7059_);
v___x_7066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7066_, 0, v_a_7061_);
lean_ctor_set(v___x_7066_, 1, v___x_7065_);
if (v_isShared_7064_ == 0)
{
lean_ctor_set(v___x_7063_, 0, v___x_7066_);
v___x_7068_ = v___x_7063_;
goto v_reusejp_7067_;
}
else
{
lean_object* v_reuseFailAlloc_7069_; 
v_reuseFailAlloc_7069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7066_);
v___x_7068_ = v_reuseFailAlloc_7069_;
goto v_reusejp_7067_;
}
v_reusejp_7067_:
{
return v___x_7068_;
}
}
}
else
{
lean_object* v_a_7071_; lean_object* v___x_7073_; uint8_t v_isShared_7074_; uint8_t v_isSharedCheck_7078_; 
lean_dec(v___x_7059_);
v_a_7071_ = lean_ctor_get(v___x_7060_, 0);
v_isSharedCheck_7078_ = !lean_is_exclusive(v___x_7060_);
if (v_isSharedCheck_7078_ == 0)
{
v___x_7073_ = v___x_7060_;
v_isShared_7074_ = v_isSharedCheck_7078_;
goto v_resetjp_7072_;
}
else
{
lean_inc(v_a_7071_);
lean_dec(v___x_7060_);
v___x_7073_ = lean_box(0);
v_isShared_7074_ = v_isSharedCheck_7078_;
goto v_resetjp_7072_;
}
v_resetjp_7072_:
{
lean_object* v___x_7076_; 
if (v_isShared_7074_ == 0)
{
v___x_7076_ = v___x_7073_;
goto v_reusejp_7075_;
}
else
{
lean_object* v_reuseFailAlloc_7077_; 
v_reuseFailAlloc_7077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_a_7071_);
v___x_7076_ = v_reuseFailAlloc_7077_;
goto v_reusejp_7075_;
}
v_reusejp_7075_:
{
return v___x_7076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_7079_, lean_object* v___y_7080_, lean_object* v___y_7081_, lean_object* v___y_7082_, lean_object* v___y_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_){
_start:
{
lean_object* v_res_7090_; 
v_res_7090_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_7079_, v___y_7080_, v___y_7081_, v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_, v___y_7088_);
lean_dec(v___y_7088_);
lean_dec_ref(v___y_7087_);
lean_dec(v___y_7086_);
lean_dec_ref(v___y_7085_);
lean_dec(v___y_7084_);
lean_dec_ref(v___y_7083_);
lean_dec(v___y_7082_);
lean_dec_ref(v___y_7081_);
lean_dec(v___y_7080_);
return v_res_7090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_7091_, lean_object* v___f_7092_, lean_object* v___y_7093_, lean_object* v___y_7094_, lean_object* v___y_7095_, lean_object* v___y_7096_, lean_object* v___y_7097_, lean_object* v___y_7098_, lean_object* v___y_7099_, lean_object* v___y_7100_, lean_object* v___y_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_){
_start:
{
lean_object* v___x_7106_; lean_object* v___x_7107_; 
v___x_7106_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_7106_, 0, v___y_7091_);
v___x_7107_ = l_Lean_Meta_Grind_Action_andThen(v___x_7106_, v___f_7092_, v___y_7093_, v___y_7094_, v___y_7095_, v___y_7096_, v___y_7097_, v___y_7098_, v___y_7099_, v___y_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_);
return v___x_7107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_7108_, lean_object* v___f_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_, lean_object* v___y_7113_, lean_object* v___y_7114_, lean_object* v___y_7115_, lean_object* v___y_7116_, lean_object* v___y_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_, lean_object* v___y_7120_, lean_object* v___y_7121_, lean_object* v___y_7122_){
_start:
{
lean_object* v_res_7123_; 
v_res_7123_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_7108_, v___f_7109_, v___y_7110_, v___y_7111_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_);
lean_dec(v___y_7121_);
lean_dec_ref(v___y_7120_);
lean_dec(v___y_7119_);
lean_dec_ref(v___y_7118_);
lean_dec(v___y_7117_);
lean_dec_ref(v___y_7116_);
lean_dec(v___y_7115_);
lean_dec_ref(v___y_7114_);
lean_dec(v___y_7113_);
return v_res_7123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_7125_, uint8_t v_compress_7126_, lean_object* v_goal_7127_, lean_object* v_kna_7128_, lean_object* v_kp_7129_, lean_object* v_a_7130_, lean_object* v_a_7131_, lean_object* v_a_7132_, lean_object* v_a_7133_, lean_object* v_a_7134_, lean_object* v_a_7135_, lean_object* v_a_7136_, lean_object* v_a_7137_, lean_object* v_a_7138_){
_start:
{
lean_object* v_toGoalState_7140_; lean_object* v_split_7141_; lean_object* v_mvarId_7142_; lean_object* v_candidates_7143_; lean_object* v___f_7144_; lean_object* v___f_7145_; lean_object* v___x_7146_; 
v_toGoalState_7140_ = lean_ctor_get(v_goal_7127_, 0);
v_split_7141_ = lean_ctor_get(v_toGoalState_7140_, 15);
v_mvarId_7142_ = lean_ctor_get(v_goal_7127_, 1);
lean_inc(v_mvarId_7142_);
v_candidates_7143_ = lean_ctor_get(v_split_7141_, 0);
lean_inc(v_candidates_7143_);
v___f_7144_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_7145_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_7145_, 0, v_goal_7127_);
v___x_7146_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_7142_, v___f_7145_, v_a_7130_, v_a_7131_, v_a_7132_, v_a_7133_, v_a_7134_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_);
if (lean_obj_tag(v___x_7146_) == 0)
{
lean_object* v_a_7147_; lean_object* v_fst_7148_; 
v_a_7147_ = lean_ctor_get(v___x_7146_, 0);
lean_inc(v_a_7147_);
lean_dec_ref_known(v___x_7146_, 1);
v_fst_7148_ = lean_ctor_get(v_a_7147_, 0);
if (lean_obj_tag(v_fst_7148_) == 1)
{
lean_object* v_snd_7149_; lean_object* v_c_7150_; lean_object* v_numCases_7151_; uint8_t v_isRec_7152_; lean_object* v___y_7154_; lean_object* v___x_7162_; lean_object* v___x_7163_; lean_object* v___x_7164_; uint8_t v___x_7167_; 
lean_inc_ref(v_fst_7148_);
v_snd_7149_ = lean_ctor_get(v_a_7147_, 1);
lean_inc(v_snd_7149_);
lean_dec(v_a_7147_);
v_c_7150_ = lean_ctor_get(v_fst_7148_, 0);
lean_inc_ref(v_c_7150_);
v_numCases_7151_ = lean_ctor_get(v_fst_7148_, 1);
lean_inc(v_numCases_7151_);
v_isRec_7152_ = lean_ctor_get_uint8(v_fst_7148_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_7148_, 2);
v___x_7162_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_7150_);
v___x_7163_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_7149_, v___x_7162_);
lean_dec_ref(v___x_7162_);
v___x_7164_ = lean_unsigned_to_nat(1u);
v___x_7167_ = lean_nat_dec_lt(v___x_7164_, v_numCases_7151_);
if (v___x_7167_ == 0)
{
if (v_isRec_7152_ == 0)
{
v___y_7154_ = v___x_7163_;
goto v___jp_7153_;
}
else
{
goto v___jp_7165_;
}
}
else
{
goto v___jp_7165_;
}
v___jp_7153_:
{
lean_object* v___f_7155_; lean_object* v___x_7156_; lean_object* v___x_7157_; lean_object* v___x_7158_; lean_object* v___x_7159_; lean_object* v___x_7160_; lean_object* v___x_7161_; 
v___f_7155_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_7155_, 0, v___y_7154_);
lean_closure_set(v___f_7155_, 1, v___f_7144_);
v___x_7156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7156_, 0, v_candidates_7143_);
v___x_7157_ = lean_box(v_isRec_7152_);
v___x_7158_ = lean_box(v_stopAtFirstFailure_7125_);
v___x_7159_ = lean_box(v_compress_7126_);
v___x_7160_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_7160_, 0, v_c_7150_);
lean_closure_set(v___x_7160_, 1, v_numCases_7151_);
lean_closure_set(v___x_7160_, 2, v___x_7157_);
lean_closure_set(v___x_7160_, 3, v___x_7158_);
lean_closure_set(v___x_7160_, 4, v___x_7159_);
lean_closure_set(v___x_7160_, 5, v___x_7156_);
v___x_7161_ = l_Lean_Meta_Grind_Action_andThen(v___x_7160_, v___f_7155_, v_snd_7149_, v_kna_7128_, v_kp_7129_, v_a_7130_, v_a_7131_, v_a_7132_, v_a_7133_, v_a_7134_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_);
return v___x_7161_;
}
v___jp_7165_:
{
lean_object* v___x_7166_; 
v___x_7166_ = lean_nat_add(v___x_7163_, v___x_7164_);
lean_dec(v___x_7163_);
v___y_7154_ = v___x_7166_;
goto v___jp_7153_;
}
}
else
{
lean_object* v_snd_7168_; lean_object* v___x_7169_; 
lean_dec(v_candidates_7143_);
lean_dec_ref(v_kp_7129_);
v_snd_7168_ = lean_ctor_get(v_a_7147_, 1);
lean_inc(v_snd_7168_);
lean_dec(v_a_7147_);
lean_inc(v_a_7138_);
lean_inc_ref(v_a_7137_);
lean_inc(v_a_7136_);
lean_inc_ref(v_a_7135_);
lean_inc(v_a_7134_);
lean_inc_ref(v_a_7133_);
lean_inc(v_a_7132_);
lean_inc_ref(v_a_7131_);
lean_inc(v_a_7130_);
v___x_7169_ = lean_apply_11(v_kna_7128_, v_snd_7168_, v_a_7130_, v_a_7131_, v_a_7132_, v_a_7133_, v_a_7134_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, lean_box(0));
return v___x_7169_;
}
}
else
{
lean_object* v_a_7170_; lean_object* v___x_7172_; uint8_t v_isShared_7173_; uint8_t v_isSharedCheck_7177_; 
lean_dec(v_candidates_7143_);
lean_dec_ref(v_kp_7129_);
lean_dec_ref(v_kna_7128_);
v_a_7170_ = lean_ctor_get(v___x_7146_, 0);
v_isSharedCheck_7177_ = !lean_is_exclusive(v___x_7146_);
if (v_isSharedCheck_7177_ == 0)
{
v___x_7172_ = v___x_7146_;
v_isShared_7173_ = v_isSharedCheck_7177_;
goto v_resetjp_7171_;
}
else
{
lean_inc(v_a_7170_);
lean_dec(v___x_7146_);
v___x_7172_ = lean_box(0);
v_isShared_7173_ = v_isSharedCheck_7177_;
goto v_resetjp_7171_;
}
v_resetjp_7171_:
{
lean_object* v___x_7175_; 
if (v_isShared_7173_ == 0)
{
v___x_7175_ = v___x_7172_;
goto v_reusejp_7174_;
}
else
{
lean_object* v_reuseFailAlloc_7176_; 
v_reuseFailAlloc_7176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7176_, 0, v_a_7170_);
v___x_7175_ = v_reuseFailAlloc_7176_;
goto v_reusejp_7174_;
}
v_reusejp_7174_:
{
return v___x_7175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_7178_, lean_object* v_compress_7179_, lean_object* v_goal_7180_, lean_object* v_kna_7181_, lean_object* v_kp_7182_, lean_object* v_a_7183_, lean_object* v_a_7184_, lean_object* v_a_7185_, lean_object* v_a_7186_, lean_object* v_a_7187_, lean_object* v_a_7188_, lean_object* v_a_7189_, lean_object* v_a_7190_, lean_object* v_a_7191_, lean_object* v_a_7192_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_7193_; uint8_t v_compress_boxed_7194_; lean_object* v_res_7195_; 
v_stopAtFirstFailure_boxed_7193_ = lean_unbox(v_stopAtFirstFailure_7178_);
v_compress_boxed_7194_ = lean_unbox(v_compress_7179_);
v_res_7195_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_7193_, v_compress_boxed_7194_, v_goal_7180_, v_kna_7181_, v_kp_7182_, v_a_7183_, v_a_7184_, v_a_7185_, v_a_7186_, v_a_7187_, v_a_7188_, v_a_7189_, v_a_7190_, v_a_7191_);
lean_dec(v_a_7191_);
lean_dec_ref(v_a_7190_);
lean_dec(v_a_7189_);
lean_dec_ref(v_a_7188_);
lean_dec(v_a_7187_);
lean_dec_ref(v_a_7186_);
lean_dec(v_a_7185_);
lean_dec_ref(v_a_7184_);
lean_dec(v_a_7183_);
return v_res_7195_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedSplitStatus_default = _init_l_Lean_Meta_Grind_instInhabitedSplitStatus_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSplitStatus_default);
l_Lean_Meta_Grind_instInhabitedSplitStatus = _init_l_Lean_Meta_Grind_instInhabitedSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSplitStatus);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Split(builtin);
}
#ifdef __cplusplus
}
#endif
