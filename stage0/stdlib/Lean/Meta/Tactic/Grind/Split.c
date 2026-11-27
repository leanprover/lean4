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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
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
v___x_1069_ = lean_alloc_ctor(0, 10, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1104_, lean_object* v_declHint_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_env_1110_; uint8_t v___x_1111_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_st_ref_get(v___y_1106_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = l_Lean_Name_isAnonymous(v_declHint_1105_);
if (v___x_1111_ == 0)
{
uint8_t v_isExporting_1112_; 
v_isExporting_1112_ = lean_ctor_get_uint8(v_env_1110_, sizeof(void*)*13);
if (v_isExporting_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v_env_1110_);
lean_dec(v_declHint_1105_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_msg_1104_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
lean_inc_ref(v_env_1110_);
v___x_1114_ = l_Lean_Environment_setExporting(v_env_1110_, v___x_1111_);
lean_inc(v_declHint_1105_);
lean_inc_ref(v___x_1114_);
v___x_1115_ = l_Lean_Environment_contains(v___x_1114_, v_declHint_1105_, v_isExporting_1112_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v___x_1114_);
lean_dec_ref(v_env_1110_);
lean_dec(v_declHint_1105_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_msg_1104_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_c_1122_; lean_object* v___x_1123_; 
v___x_1117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1119_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1114_);
v___x_1120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1114_);
lean_ctor_set(v___x_1120_, 1, v___x_1117_);
lean_ctor_set(v___x_1120_, 2, v___x_1118_);
lean_ctor_set(v___x_1120_, 3, v___x_1119_);
lean_inc(v_declHint_1105_);
v___x_1121_ = l_Lean_MessageData_ofConstName(v_declHint_1105_, v___x_1111_);
v_c_1122_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1122_, 0, v___x_1120_);
lean_ctor_set(v_c_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1114_, v_declHint_1105_);
lean_dec_ref(v___x_1114_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v_env_1110_);
lean_dec(v_declHint_1105_);
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_c_1122_);
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_MessageData_note(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_msg_1104_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1165_; 
v_val_1131_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1133_ = v___x_1123_;
v_isShared_1134_ = v_isSharedCheck_1165_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v___x_1123_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1165_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v_moduleNames_1136_; lean_object* v_mod_1137_; uint8_t v___x_1138_; 
v___x_1135_ = l_Lean_Environment_header(v_env_1110_);
lean_dec_ref(v_env_1110_);
v_moduleNames_1136_ = lean_ctor_get(v___x_1135_, 4);
lean_inc_ref(v_moduleNames_1136_);
lean_dec_ref(v___x_1135_);
v_mod_1137_ = lean_array_get(v___x_1108_, v_moduleNames_1136_, v_val_1131_);
lean_dec(v_val_1131_);
lean_dec_ref(v_moduleNames_1136_);
v___x_1138_ = l_Lean_isPrivateName(v_declHint_1105_);
lean_dec(v_declHint_1105_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v_c_1122_);
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_MessageData_ofName(v_mod_1137_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_MessageData_note(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_msg_1104_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1148_);
v___x_1150_ = v___x_1133_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_c_1122_);
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofName(v_mod_1137_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_note(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_msg_1104_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1161_);
v___x_1163_ = v___x_1133_;
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
lean_object* v___x_1166_; 
lean_dec_ref(v_env_1110_);
lean_dec(v_declHint_1105_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_msg_1104_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1167_, lean_object* v_declHint_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1167_, v_declHint_1168_, v___y_1169_);
lean_dec(v___y_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1172_, lean_object* v_declHint_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1195_; 
v___x_1185_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1172_, v_declHint_1173_, v___y_1183_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1190_ = l_Lean_unknownIdentifierMessageTag;
v___x_1191_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v_a_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1196_, lean_object* v_declHint_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1196_, v_declHint_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_env_1217_; uint8_t v___x_1218_; lean_object* v_env_1219_; lean_object* v___x_1220_; lean_object* v_toCold_1221_; lean_object* v_mctx_1222_; lean_object* v_lctx_1223_; lean_object* v_options_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v___x_1218_ = 0;
v_env_1219_ = l_Lean_Environment_setRecordingDeps(v_env_1217_, v___x_1218_);
v___x_1220_ = lean_st_ref_get(v___y_1212_);
v_toCold_1221_ = lean_ctor_get(v___y_1213_, 0);
v_mctx_1222_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_mctx_1222_);
lean_dec(v___x_1220_);
v_lctx_1223_ = lean_ctor_get(v___y_1211_, 2);
v_options_1224_ = lean_ctor_get(v_toCold_1221_, 2);
lean_inc_ref(v_options_1224_);
lean_inc_ref(v_lctx_1223_);
v___x_1225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1225_, 0, v_env_1219_);
lean_ctor_set(v___x_1225_, 1, v_mctx_1222_);
lean_ctor_set(v___x_1225_, 2, v_lctx_1223_);
lean_ctor_set(v___x_1225_, 3, v_options_1224_);
v___x_1226_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_msgData_1210_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_ref_1241_; lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
v_ref_1241_ = lean_ctor_get(v___y_1238_, 2);
v___x_1242_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_inc(v_ref_1241_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_ref_1241_);
lean_ctor_set(v___x_1247_, 1, v_a_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 1);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_toCold_1272_; lean_object* v_currRecDepth_1273_; lean_object* v_ref_1274_; uint16_t v_optionFlags_1275_; uint8_t v_suppressElabErrors_1276_; uint8_t v_checkDeprecated_1277_; uint8_t v_isRecordingDeps_1278_; lean_object* v_ref_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_toCold_1272_ = lean_ctor_get(v___y_1269_, 0);
v_currRecDepth_1273_ = lean_ctor_get(v___y_1269_, 1);
v_ref_1274_ = lean_ctor_get(v___y_1269_, 2);
v_optionFlags_1275_ = lean_ctor_get_uint16(v___y_1269_, sizeof(void*)*3);
v_suppressElabErrors_1276_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*3 + 2);
v_checkDeprecated_1277_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1278_ = lean_ctor_get_uint8(v___y_1269_, sizeof(void*)*3 + 4);
v_ref_1279_ = l_Lean_replaceRef(v_ref_1259_, v_ref_1274_);
lean_inc(v_currRecDepth_1273_);
lean_inc_ref(v_toCold_1272_);
v___x_1280_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1280_, 0, v_toCold_1272_);
lean_ctor_set(v___x_1280_, 1, v_currRecDepth_1273_);
lean_ctor_set(v___x_1280_, 2, v_ref_1279_);
lean_ctor_set_uint16(v___x_1280_, sizeof(void*)*3, v_optionFlags_1275_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 2, v_suppressElabErrors_1276_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 3, v_checkDeprecated_1277_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 4, v_isRecordingDeps_1278_);
v___x_1281_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1260_, v___y_1267_, v___y_1268_, v___x_1280_, v___y_1270_);
lean_dec_ref_known(v___x_1280_, 3);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1282_, v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v_ref_1282_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1296_, lean_object* v_msg_1297_, lean_object* v_declHint_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v_a_1311_; lean_object* v___x_1312_; 
v___x_1310_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1297_, v_declHint_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1296_, v_a_1311_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1313_, lean_object* v_msg_1314_, lean_object* v_declHint_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1313_, v_msg_1314_, v_declHint_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec(v_ref_1313_);
return v_res_1327_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1334_, lean_object* v_constName_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1347_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1348_ = 0;
lean_inc(v_constName_1335_);
v___x_1349_ = l_Lean_MessageData_ofConstName(v_constName_1335_, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1347_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1334_, v___x_1352_, v_constName_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1354_, lean_object* v_constName_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1354_, v_constName_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec(v_ref_1354_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_ref_1380_; lean_object* v___x_1381_; 
v_ref_1380_ = lean_ctor_get(v___y_1377_, 2);
v___x_1381_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1380_, v_constName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; lean_object* v_env_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = lean_st_ref_get(v___y_1405_);
v_env_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_env_1408_);
lean_dec(v___x_1407_);
v___x_1409_ = 0;
lean_inc(v_constName_1395_);
v___x_1410_ = l_Lean_Environment_find_x3f(v_env_1408_, v_constName_1395_, v___x_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1411_;
}
else
{
lean_object* v_val_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_constName_1395_);
v_val_1412_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1410_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_val_1412_);
lean_dec(v___x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 0);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_val_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
return v_res_1432_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1433_; double v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_float_of_nat(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1438_, lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_ref_1445_; lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1492_; 
v_ref_1445_ = lean_ctor_get(v___y_1442_, 2);
v___x_1446_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1492_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1492_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v_traceState_1452_; lean_object* v_env_1453_; lean_object* v_nextMacroScope_1454_; lean_object* v_ngen_1455_; lean_object* v_auxDeclNGen_1456_; lean_object* v_cache_1457_; lean_object* v_recordedDeps_1458_; lean_object* v_messages_1459_; lean_object* v_infoState_1460_; lean_object* v_snapshotTasks_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1491_; 
v___x_1451_ = lean_st_ref_take(v___y_1443_);
v_traceState_1452_ = lean_ctor_get(v___x_1451_, 4);
v_env_1453_ = lean_ctor_get(v___x_1451_, 0);
v_nextMacroScope_1454_ = lean_ctor_get(v___x_1451_, 1);
v_ngen_1455_ = lean_ctor_get(v___x_1451_, 2);
v_auxDeclNGen_1456_ = lean_ctor_get(v___x_1451_, 3);
v_cache_1457_ = lean_ctor_get(v___x_1451_, 5);
v_recordedDeps_1458_ = lean_ctor_get(v___x_1451_, 6);
v_messages_1459_ = lean_ctor_get(v___x_1451_, 7);
v_infoState_1460_ = lean_ctor_get(v___x_1451_, 8);
v_snapshotTasks_1461_ = lean_ctor_get(v___x_1451_, 9);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1463_ = v___x_1451_;
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snapshotTasks_1461_);
lean_inc(v_infoState_1460_);
lean_inc(v_messages_1459_);
lean_inc(v_recordedDeps_1458_);
lean_inc(v_cache_1457_);
lean_inc(v_traceState_1452_);
lean_inc(v_auxDeclNGen_1456_);
lean_inc(v_ngen_1455_);
lean_inc(v_nextMacroScope_1454_);
lean_inc(v_env_1453_);
lean_dec(v___x_1451_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
uint64_t v_tid_1465_; lean_object* v_traces_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v_tid_1465_ = lean_ctor_get_uint64(v_traceState_1452_, sizeof(void*)*1);
v_traces_1466_ = lean_ctor_get(v_traceState_1452_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_traceState_1452_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v_traceState_1452_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_traces_1466_);
lean_dec(v_traceState_1452_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; double v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1473_ = 0;
v___x_1474_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1475_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1475_, 0, v_cls_1438_);
lean_ctor_set(v___x_1475_, 1, v___x_1471_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
lean_ctor_set_float(v___x_1475_, sizeof(void*)*3, v___x_1472_);
lean_ctor_set_float(v___x_1475_, sizeof(void*)*3 + 8, v___x_1472_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*3 + 16, v___x_1473_);
v___x_1476_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1477_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v_a_1447_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
lean_inc(v_ref_1445_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_ref_1445_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_PersistentArray_push___redArg(v_traces_1466_, v___x_1478_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1479_);
v___x_1481_ = v___x_1468_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1479_);
lean_ctor_set_uint64(v_reuseFailAlloc_1489_, sizeof(void*)*1, v_tid_1465_);
v___x_1481_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1481_);
v___x_1483_ = v___x_1463_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_env_1453_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_nextMacroScope_1454_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_ngen_1455_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_auxDeclNGen_1456_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 5, v_cache_1457_);
lean_ctor_set(v_reuseFailAlloc_1488_, 6, v_recordedDeps_1458_);
lean_ctor_set(v_reuseFailAlloc_1488_, 7, v_messages_1459_);
lean_ctor_set(v_reuseFailAlloc_1488_, 8, v_infoState_1460_);
lean_ctor_set(v_reuseFailAlloc_1488_, 9, v_snapshotTasks_1461_);
v___x_1483_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_st_ref_put(v___y_1443_, v___x_1483_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1470_);
v___x_1486_ = v___x_1449_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1470_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1519_ = l_Lean_Name_append(v___x_1518_, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; uint8_t v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___x_1796_; 
lean_inc_ref(v_e_1535_);
v___x_1796_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1535_, v_a_1543_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1828_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1828_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1828_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = l_Lean_Expr_cleanupAnnotations(v_a_1797_);
lean_dec(v_a_1797_);
v___x_1802_ = l_Lean_Expr_isApp(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1801_);
lean_del_object(v___x_1799_);
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
v___y_1684_ = v_a_1544_;
v___y_1685_ = v_a_1545_;
goto v___jp_1675_;
}
else
{
lean_object* v_arg_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_arg_1803_ = lean_ctor_get(v___x_1801_, 1);
lean_inc_ref(v_arg_1803_);
v___x_1804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1806_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_Expr_isApp(v___x_1804_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1799_);
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
v___y_1684_ = v_a_1544_;
v___y_1685_ = v_a_1545_;
goto v___jp_1675_;
}
else
{
lean_object* v_arg_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_arg_1808_ = lean_ctor_get(v___x_1804_, 1);
lean_inc_ref(v_arg_1808_);
v___x_1809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1811_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1813_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1812_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Lean_Expr_isApp(v___x_1809_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1799_);
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
v___y_1684_ = v_a_1544_;
v___y_1685_ = v_a_1545_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1809_);
lean_dec_ref(v___x_1809_);
v___x_1816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20));
v___x_1817_ = l_Lean_Expr_isConstOf(v___x_1815_, v___x_1816_);
lean_dec_ref(v___x_1815_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1799_);
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
v___y_1684_ = v_a_1544_;
v___y_1685_ = v_a_1545_;
goto v___jp_1675_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1535_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_e_1535_);
v___x_1819_ = lean_unsigned_to_nat(2u);
v___x_1820_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*1, v___x_1818_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*1 + 1, v___x_1818_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1820_);
v___x_1822_ = v___x_1799_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
lean_object* v___x_1824_; 
lean_del_object(v___x_1799_);
v___x_1824_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1535_, v_arg_1808_, v_arg_1803_, v_a_1536_, v_a_1540_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1824_;
}
}
}
}
else
{
lean_object* v___x_1825_; 
lean_dec_ref(v___x_1809_);
lean_del_object(v___x_1799_);
v___x_1825_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1535_, v_arg_1808_, v_arg_1803_, v_a_1536_, v_a_1540_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1825_;
}
}
else
{
lean_object* v___x_1826_; 
lean_dec_ref(v___x_1809_);
lean_del_object(v___x_1799_);
v___x_1826_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1535_, v_arg_1808_, v_arg_1803_, v_a_1536_, v_a_1540_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1826_;
}
}
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref(v___x_1804_);
lean_del_object(v___x_1799_);
lean_dec_ref(v_e_1535_);
v___x_1827_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v_arg_1803_, v_a_1536_, v_a_1540_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_e_1535_);
v_a_1829_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1796_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1796_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
v___jp_1547_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
v___jp_1550_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
v___jp_1553_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
v___jp_1556_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = l_Lean_Expr_getAppNumArgs(v_e_1535_);
v___x_1565_ = lean_nat_sub(v___x_1564_, v___x_1563_);
lean_dec(v___x_1564_);
v___x_1566_ = lean_nat_sub(v___x_1565_, v___x_1563_);
lean_dec(v___x_1565_);
v___x_1567_ = l_Lean_Expr_getRevArg_x21(v_e_1535_, v___x_1566_);
lean_dec_ref(v_e_1535_);
v___x_1568_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v___x_1567_, v___y_1559_, v___y_1561_, v___y_1558_, v___y_1557_, v___y_1562_, v___y_1560_);
return v___x_1568_;
}
v___jp_1569_:
{
uint8_t v___x_1581_; 
v___x_1581_ = l_Lean_Expr_isFVar(v_e_1535_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v_e_1535_);
v___x_1582_ = lean_box(1);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; 
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc_ref(v_e_1535_);
v___x_1584_ = lean_infer_type(v_e_1535_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l_Lean_Meta_whnfD(v_a_1585_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_n(v_a_1587_, 2);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1589_ = l_Lean_MessageData_ofExpr(v_e_1535_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_indentExpr(v_a_1587_);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Expr_getAppFn(v_a_1587_);
lean_dec(v_a_1587_);
if (lean_obj_tag(v___x_1595_) == 4)
{
lean_object* v_declName_1596_; lean_object* v___x_1597_; 
v_declName_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_declName_1596_);
lean_dec_ref_known(v___x_1595_, 2);
v___x_1597_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1596_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1630_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1630_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1630_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
if (lean_obj_tag(v_a_1598_) == 5)
{
lean_object* v_val_1602_; lean_object* v_ctors_1603_; uint8_t v_isRec_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_dec_ref_known(v___x_1594_, 2);
v_val_1602_ = lean_ctor_get(v_a_1598_, 0);
lean_inc_ref(v_val_1602_);
lean_dec_ref_known(v_a_1598_, 1);
v_ctors_1603_ = lean_ctor_get(v_val_1602_, 4);
lean_inc(v_ctors_1603_);
v_isRec_1604_ = lean_ctor_get_uint8(v_val_1602_, sizeof(void*)*6);
lean_dec_ref(v_val_1602_);
v___x_1605_ = l_List_lengthTR___redArg(v_ctors_1603_);
lean_dec(v_ctors_1603_);
v___x_1606_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*1, v_isRec_1604_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*1 + 1, v___y_1570_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1606_);
v___x_1608_ = v___x_1600_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
else
{
lean_object* v___x_1610_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v___x_1610_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1575_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; uint8_t v_verbose_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v_verbose_1612_ = lean_ctor_get_uint8(v_a_1611_, 0);
lean_dec(v_a_1611_);
if (v_verbose_1612_ == 0)
{
lean_dec_ref_known(v___x_1594_, 2);
goto v___jp_1550_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_Sym_reportIssue(v___x_1594_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec_ref_known(v___x_1613_, 1);
goto v___jp_1550_;
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
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
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref_known(v___x_1594_, 2);
v_a_1622_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1610_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1610_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref_known(v___x_1594_, 2);
v_a_1631_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1597_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1597_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; 
lean_dec_ref(v___x_1595_);
v___x_1639_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1575_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; uint8_t v_verbose_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v_verbose_1641_ = lean_ctor_get_uint8(v_a_1640_, 0);
lean_dec(v_a_1640_);
if (v_verbose_1641_ == 0)
{
lean_dec_ref_known(v___x_1594_, 2);
goto v___jp_1553_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Sym_reportIssue(v___x_1594_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec_ref_known(v___x_1642_, 1);
goto v___jp_1553_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref_known(v___x_1594_, 2);
v_a_1651_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1639_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1639_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_e_1535_);
v_a_1659_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1586_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1586_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_e_1535_);
v_a_1667_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1584_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1584_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
v___jp_1675_:
{
uint8_t v___x_1686_; 
v___x_1686_ = l_Lean_Meta_Grind_isIte(v_e_1535_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = l_Lean_Meta_Grind_isDIte(v_e_1535_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1535_, v___y_1676_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_inc_ref(v_e_1535_);
v___x_1691_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1535_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1751_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1751_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1751_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_unbox(v_a_1692_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_st_ref_get(v___y_1685_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1699_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1698_, v_e_1535_);
if (lean_obj_tag(v___x_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1706_; 
lean_dec_ref(v_e_1535_);
v_val_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1700_);
lean_dec(v_val_1700_);
v___x_1702_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
v___x_1703_ = lean_unbox(v_a_1692_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*1, v___x_1703_);
v___x_1704_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*1 + 1, v___x_1704_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1702_);
v___x_1706_ = v___x_1694_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1702_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_object* v___x_1708_; 
lean_dec(v___x_1699_);
lean_del_object(v___x_1694_);
v___x_1708_ = l_Lean_Expr_getAppFn(v_e_1535_);
if (lean_obj_tag(v___x_1708_) == 4)
{
lean_object* v_declName_1709_; lean_object* v___x_1710_; 
v_declName_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_declName_1709_);
lean_dec_ref_known(v___x_1708_, 2);
v___x_1710_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1709_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
if (lean_obj_tag(v_a_1711_) == 1)
{
lean_object* v_val_1712_; lean_object* v___x_1713_; 
v_val_1712_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_val_1712_);
lean_dec_ref_known(v_a_1711_, 1);
lean_inc_ref(v_e_1535_);
v___x_1713_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1535_, v___y_1676_, v___y_1680_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1728_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1728_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1728_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_unbox(v_a_1714_);
lean_dec(v_a_1714_);
if (v___x_1718_ == 0)
{
uint8_t v___x_1719_; 
lean_del_object(v___x_1716_);
lean_dec(v_val_1712_);
v___x_1719_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
v___y_1570_ = v___x_1719_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
v___y_1579_ = v___y_1684_;
v___y_1580_ = v___y_1685_;
goto v___jp_1569_;
}
else
{
lean_object* v_ctors_1720_; uint8_t v_isRec_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1726_; 
lean_dec_ref(v_e_1535_);
v_ctors_1720_ = lean_ctor_get(v_val_1712_, 4);
lean_inc(v_ctors_1720_);
v_isRec_1721_ = lean_ctor_get_uint8(v_val_1712_, sizeof(void*)*6);
lean_dec(v_val_1712_);
v___x_1722_ = l_List_lengthTR___redArg(v_ctors_1720_);
lean_dec(v_ctors_1720_);
v___x_1723_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set_uint8(v___x_1723_, sizeof(void*)*1, v_isRec_1721_);
v___x_1724_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
lean_ctor_set_uint8(v___x_1723_, sizeof(void*)*1 + 1, v___x_1724_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1723_);
v___x_1726_ = v___x_1716_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1723_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_val_1712_);
lean_dec(v_a_1692_);
lean_dec_ref(v_e_1535_);
v_a_1729_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1713_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1713_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
uint8_t v___x_1737_; 
lean_dec(v_a_1711_);
v___x_1737_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
v___y_1570_ = v___x_1737_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
v___y_1579_ = v___y_1684_;
v___y_1580_ = v___y_1685_;
goto v___jp_1569_;
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_a_1692_);
lean_dec_ref(v_e_1535_);
v_a_1738_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1710_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1710_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
uint8_t v___x_1746_; 
lean_dec_ref(v___x_1708_);
v___x_1746_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
v___y_1570_ = v___x_1746_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
v___y_1579_ = v___y_1684_;
v___y_1580_ = v___y_1685_;
goto v___jp_1569_;
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v_a_1692_);
lean_dec_ref(v_e_1535_);
v___x_1747_ = lean_box(0);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1747_);
v___x_1749_ = v___x_1694_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_e_1535_);
v_a_1752_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1691_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1691_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
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
lean_object* v_toCold_1760_; lean_object* v_options_1761_; uint8_t v_hasTrace_1762_; 
v_toCold_1760_ = lean_ctor_get(v___y_1684_, 0);
v_options_1761_ = lean_ctor_get(v_toCold_1760_, 2);
v_hasTrace_1762_ = lean_ctor_get_uint8(v_options_1761_, sizeof(void*)*1);
if (v_hasTrace_1762_ == 0)
{
lean_dec_ref(v_e_1535_);
goto v___jp_1547_;
}
else
{
lean_object* v_inheritedTraceOptions_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_inheritedTraceOptions_1763_ = lean_ctor_get(v_toCold_1760_, 11);
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1763_, v_options_1761_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec_ref(v_e_1535_);
goto v___jp_1547_;
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Meta_Grind_updateLastTag(v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1769_ = l_Lean_MessageData_ofExpr(v_e_1535_);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1764_, v___x_1770_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_dec_ref_known(v___x_1771_, 1);
goto v___jp_1547_;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_e_1535_);
v_a_1780_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1767_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1767_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_e_1535_);
v_a_1788_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1688_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1688_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
v___y_1557_ = v___y_1683_;
v___y_1558_ = v___y_1682_;
v___y_1559_ = v___y_1676_;
v___y_1560_ = v___y_1685_;
v___y_1561_ = v___y_1680_;
v___y_1562_ = v___y_1684_;
goto v___jp_1556_;
}
}
else
{
v___y_1557_ = v___y_1683_;
v___y_1558_ = v___y_1682_;
v___y_1559_ = v___y_1676_;
v___y_1560_ = v___y_1685_;
v___y_1561_ = v___y_1680_;
v___y_1562_ = v___y_1684_;
goto v___jp_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec(v_a_1838_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1850_, v_msg_1851_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1864_, lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1864_, v_msg_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec(v___y_1866_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1878_, lean_object* v_constName_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_constName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1892_, v_constName_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec(v___y_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1906_, lean_object* v_ref_1907_, lean_object* v_constName_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1907_, v_constName_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_ref_1922_, lean_object* v_constName_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1921_, v_ref_1922_, v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec(v_ref_1922_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1936_, lean_object* v_ref_1937_, lean_object* v_msg_1938_, lean_object* v_declHint_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1937_, v_msg_1938_, v_declHint_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_ref_1953_, lean_object* v_msg_1954_, lean_object* v_declHint_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1952_, v_ref_1953_, v_msg_1954_, v_declHint_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v_ref_1953_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1968_, lean_object* v_declHint_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1968_, v_declHint_1969_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1982_, lean_object* v_declHint_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1982_, v_declHint_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1996_, lean_object* v_ref_1997_, lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1997_, v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_ref_2012_, lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2011_, v_ref_2012_, v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec(v_ref_2012_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2027_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_msg_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2040_, v_msg_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2054_, lean_object* v_x_2055_){
_start:
{
if (lean_obj_tag(v_x_2055_) == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_box(0);
return v___x_2056_;
}
else
{
lean_object* v_key_2057_; lean_object* v_value_2058_; lean_object* v_tail_2059_; lean_object* v_fst_2060_; lean_object* v_snd_2061_; lean_object* v_fst_2062_; lean_object* v_snd_2063_; uint8_t v___x_2064_; 
v_key_2057_ = lean_ctor_get(v_x_2055_, 0);
v_value_2058_ = lean_ctor_get(v_x_2055_, 1);
v_tail_2059_ = lean_ctor_get(v_x_2055_, 2);
v_fst_2060_ = lean_ctor_get(v_key_2057_, 0);
v_snd_2061_ = lean_ctor_get(v_key_2057_, 1);
v_fst_2062_ = lean_ctor_get(v_a_2054_, 0);
v_snd_2063_ = lean_ctor_get(v_a_2054_, 1);
v___x_2064_ = lean_expr_eqv(v_fst_2060_, v_fst_2062_);
if (v___x_2064_ == 0)
{
v_x_2055_ = v_tail_2059_;
goto _start;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_expr_eqv(v_snd_2061_, v_snd_2063_);
if (v___x_2066_ == 0)
{
v_x_2055_ = v_tail_2059_;
goto _start;
}
else
{
lean_object* v___x_2068_; 
lean_inc(v_value_2058_);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_value_2058_);
return v___x_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2069_, v_x_2070_);
lean_dec(v_x_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_buckets_2074_; lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2077_; uint64_t v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; uint64_t v___x_2082_; uint64_t v_fold_2083_; uint64_t v___x_2084_; uint64_t v___x_2085_; uint64_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_buckets_2074_ = lean_ctor_get(v_m_2072_, 1);
v_fst_2075_ = lean_ctor_get(v_a_2073_, 0);
v_snd_2076_ = lean_ctor_get(v_a_2073_, 1);
v___x_2077_ = lean_array_get_size(v_buckets_2074_);
v___x_2078_ = l_Lean_Expr_hash(v_fst_2075_);
v___x_2079_ = l_Lean_Expr_hash(v_snd_2076_);
v___x_2080_ = lean_uint64_mix_hash(v___x_2078_, v___x_2079_);
v___x_2081_ = 32ULL;
v___x_2082_ = lean_uint64_shift_right(v___x_2080_, v___x_2081_);
v_fold_2083_ = lean_uint64_xor(v___x_2080_, v___x_2082_);
v___x_2084_ = 16ULL;
v___x_2085_ = lean_uint64_shift_right(v_fold_2083_, v___x_2084_);
v___x_2086_ = lean_uint64_xor(v_fold_2083_, v___x_2085_);
v___x_2087_ = lean_uint64_to_usize(v___x_2086_);
v___x_2088_ = lean_usize_of_nat(v___x_2077_);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_sub(v___x_2088_, v___x_2089_);
v___x_2091_ = lean_usize_land(v___x_2087_, v___x_2090_);
v___x_2092_ = lean_array_uget_borrowed(v_buckets_2074_, v___x_2091_);
v___x_2093_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2073_, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2094_, v_a_2095_);
lean_dec_ref(v_a_2095_);
lean_dec_ref(v_m_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2097_, uint8_t v___x_2098_, lean_object* v_fst_2099_, lean_object* v_snd_2100_, lean_object* v___x_2101_, lean_object* v_____r_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2114_ = lean_unsigned_to_nat(2u);
v___x_2115_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1, v_a_2097_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 1, v___x_2098_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v_fst_2099_);
lean_ctor_set(v___x_2117_, 1, v_snd_2100_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2101_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2122_ = _args[0];
lean_object* v___x_2123_ = _args[1];
lean_object* v_fst_2124_ = _args[2];
lean_object* v_snd_2125_ = _args[3];
lean_object* v___x_2126_ = _args[4];
lean_object* v_____r_2127_ = _args[5];
lean_object* v___y_2128_ = _args[6];
lean_object* v___y_2129_ = _args[7];
lean_object* v___y_2130_ = _args[8];
lean_object* v___y_2131_ = _args[9];
lean_object* v___y_2132_ = _args[10];
lean_object* v___y_2133_ = _args[11];
lean_object* v___y_2134_ = _args[12];
lean_object* v___y_2135_ = _args[13];
lean_object* v___y_2136_ = _args[14];
lean_object* v___y_2137_ = _args[15];
lean_object* v___y_2138_ = _args[16];
_start:
{
uint8_t v_a_34317__boxed_2139_; uint8_t v___x_34318__boxed_2140_; lean_object* v_res_2141_; 
v_a_34317__boxed_2139_ = lean_unbox(v_a_2122_);
v___x_34318__boxed_2140_ = lean_unbox(v___x_2123_);
v_res_2141_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34317__boxed_2139_, v___x_34318__boxed_2140_, v_fst_2124_, v_snd_2125_, v___x_2126_, v_____r_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec(v___y_2128_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2142_, lean_object* v_snd_2143_, lean_object* v___x_2144_, lean_object* v___x_2145_, lean_object* v_____r_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2158_ = l_Lean_Expr_appFn_x21(v_fst_2142_);
v___x_2159_ = l_Lean_Expr_appFn_x21(v_snd_2143_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2144_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2145_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2165_, lean_object* v_snd_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_____r_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2165_, v_snd_2166_, v___x_2167_, v___x_2168_, v_____r_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec(v_snd_2166_);
lean_dec(v_fst_2165_);
return v_res_2181_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___f_2183_; 
v___x_2182_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2183_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2183_, 0, v___x_2182_);
return v___f_2183_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2189_ = l_Lean_Name_append(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2208_, lean_object* v___y_2209_, lean_object* v_eq_2210_, lean_object* v_a_2211_, lean_object* v_b_2212_, lean_object* v_a_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___y_2226_; lean_object* v_snd_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2368_; 
v_snd_2246_ = lean_ctor_get(v_a_2213_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_a_2213_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v_a_2213_, 0);
lean_dec(v_unused_2369_);
v___x_2248_ = v_a_2213_;
v_isShared_2249_ = v_isSharedCheck_2368_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snd_2246_);
lean_dec(v_a_2213_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2368_;
goto v_resetjp_2247_;
}
v___jp_2225_:
{
if (lean_obj_tag(v___y_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2237_; 
v_a_2227_ = lean_ctor_get(v___y_2226_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___y_2226_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2229_ = v___y_2226_;
v_isShared_2230_ = v_isSharedCheck_2237_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___y_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2237_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
if (lean_obj_tag(v_a_2227_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; 
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v_a_2231_ = lean_ctor_get(v_a_2227_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v_a_2227_, 1);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v_a_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
else
{
lean_object* v_a_2235_; 
lean_del_object(v___x_2229_);
v_a_2235_ = lean_ctor_get(v_a_2227_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v_a_2227_, 1);
v_a_2213_ = v_a_2235_;
goto _start;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v_a_2238_ = lean_ctor_get(v___y_2226_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___y_2226_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___y_2226_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___y_2226_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v_resetjp_2247_:
{
lean_object* v_snd_2250_; lean_object* v_fst_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2367_; 
v_snd_2250_ = lean_ctor_get(v_snd_2246_, 1);
v_fst_2251_ = lean_ctor_get(v_snd_2246_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_snd_2246_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2253_ = v_snd_2246_;
v_isShared_2254_ = v_isSharedCheck_2367_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2250_);
lean_inc(v_fst_2251_);
lean_dec(v_snd_2246_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2367_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_fst_2255_; lean_object* v_snd_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2366_; 
v_fst_2255_ = lean_ctor_get(v_snd_2250_, 0);
v_snd_2256_ = lean_ctor_get(v_snd_2250_, 1);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_snd_2250_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2258_ = v_snd_2250_;
v_isShared_2259_ = v_isSharedCheck_2366_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_snd_2256_);
lean_inc(v_fst_2255_);
lean_dec(v_snd_2250_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2366_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
uint8_t v___y_2261_; uint8_t v___x_2275_; 
v___x_2275_ = l_Lean_Expr_isApp(v_fst_2255_);
if (v___x_2275_ == 0)
{
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v___y_2261_ = v_a_2208_;
goto v___jp_2260_;
}
else
{
uint8_t v___x_2276_; 
v___x_2276_ = l_Lean_Expr_isApp(v_snd_2256_);
if (v___x_2276_ == 0)
{
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v___y_2261_ = v___x_2276_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___f_2280_; uint8_t v___x_2281_; 
lean_del_object(v___x_2258_);
lean_del_object(v___x_2253_);
lean_del_object(v___x_2248_);
v___x_2277_ = lean_box(0);
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_nat_sub(v_fst_2251_, v___x_2278_);
lean_dec(v_fst_2251_);
v___f_2280_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2209_);
lean_inc(v___x_2279_);
v___x_2281_ = l_List_elem___redArg(v___f_2280_, v___x_2279_, v___y_2209_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = l_Lean_Expr_appArg_x21(v_fst_2255_);
v___x_2283_ = l_Lean_Expr_appArg_x21(v_snd_2256_);
v___x_2284_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2282_, v___x_2283_, v___y_2214_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; uint8_t v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = lean_unbox(v_a_2285_);
if (v___x_2286_ == 0)
{
lean_object* v_toCold_2287_; lean_object* v_options_2288_; lean_object* v_inheritedTraceOptions_2289_; uint8_t v_hasTrace_2290_; 
v_toCold_2287_ = lean_ctor_get(v___y_2222_, 0);
v_options_2288_ = lean_ctor_get(v_toCold_2287_, 2);
v_inheritedTraceOptions_2289_ = lean_ctor_get(v_toCold_2287_, 11);
v_hasTrace_2290_ = lean_ctor_get_uint8(v_options_2288_, sizeof(void*)*1);
if (v_hasTrace_2290_ == 0)
{
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
goto v___jp_2291_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2295_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2296_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2289_, v_options_2288_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
goto v___jp_2291_;
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Meta_Grind_updateLastTag(v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v___x_2299_; 
lean_dec_ref_known(v___x_2298_, 1);
v___x_2299_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2210_, v___y_2214_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2211_);
v___x_2302_ = l_Lean_MessageData_ofExpr(v_a_2211_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
lean_inc_ref(v_b_2212_);
v___x_2306_ = l_Lean_MessageData_ofExpr(v_b_2212_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
lean_inc_ref(v_eq_2210_);
v___x_2310_ = l_Lean_MessageData_ofExpr(v_eq_2210_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = l_Lean_MessageData_ofExpr(v___x_2282_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_MessageData_ofExpr(v___x_2283_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Nat_reprFast(v_a_2300_);
v___x_2323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v___x_2324_ = l_Lean_MessageData_ofFormat(v___x_2323_);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2321_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2295_, v___x_2325_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = lean_unbox(v_a_2285_);
lean_dec(v_a_2285_);
v___x_2329_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2328_, v___x_2276_, v_fst_2255_, v_snd_2256_, v___x_2279_, v_a_2327_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
v___y_2226_ = v___x_2329_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_a_2285_);
lean_dec(v___x_2279_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v_a_2330_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2326_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2326_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2285_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec(v___x_2279_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v_a_2338_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2299_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2299_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2285_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec(v___x_2279_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v_a_2346_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2298_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2298_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
v___jp_2291_:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_unbox(v_a_2285_);
lean_dec(v_a_2285_);
v___x_2294_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2293_, v___x_2276_, v_fst_2255_, v_snd_2256_, v___x_2279_, v___x_2292_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
v___y_2226_ = v___x_2294_;
goto v___jp_2225_;
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec(v_a_2285_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
v___x_2354_ = lean_box(0);
v___x_2355_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2255_, v_snd_2256_, v___x_2279_, v___x_2277_, v___x_2354_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
v___y_2226_ = v___x_2355_;
goto v___jp_2225_;
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec(v___x_2279_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
lean_dec_ref(v_b_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_eq_2210_);
lean_dec(v___y_2209_);
v_a_2356_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2284_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2284_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2255_, v_snd_2256_, v___x_2279_, v___x_2277_, v___x_2364_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
v___y_2226_ = v___x_2365_;
goto v___jp_2225_;
}
}
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2262_ = lean_unsigned_to_nat(2u);
v___x_2263_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*1, v___y_2261_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*1 + 1, v___y_2261_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
if (v_isShared_2259_ == 0)
{
v___x_2266_ = v___x_2258_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_fst_2255_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_snd_2256_);
v___x_2266_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v___x_2266_);
v___x_2268_ = v___x_2253_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_fst_2251_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2268_);
lean_ctor_set(v___x_2248_, 0, v___x_2264_);
v___x_2270_ = v___x_2248_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; 
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
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
lean_object* v_a_2370_ = _args[0];
lean_object* v___y_2371_ = _args[1];
lean_object* v_eq_2372_ = _args[2];
lean_object* v_a_2373_ = _args[3];
lean_object* v_b_2374_ = _args[4];
lean_object* v_a_2375_ = _args[5];
lean_object* v___y_2376_ = _args[6];
lean_object* v___y_2377_ = _args[7];
lean_object* v___y_2378_ = _args[8];
lean_object* v___y_2379_ = _args[9];
lean_object* v___y_2380_ = _args[10];
lean_object* v___y_2381_ = _args[11];
lean_object* v___y_2382_ = _args[12];
lean_object* v___y_2383_ = _args[13];
lean_object* v___y_2384_ = _args[14];
lean_object* v___y_2385_ = _args[15];
lean_object* v___y_2386_ = _args[16];
_start:
{
uint8_t v_a_34491__boxed_2387_; lean_object* v_res_2388_; 
v_a_34491__boxed_2387_ = lean_unbox(v_a_2370_);
v_res_2388_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34491__boxed_2387_, v___y_2371_, v_eq_2372_, v_a_2373_, v_b_2374_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2389_, lean_object* v_b_2390_, lean_object* v_eq_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2406_; 
lean_inc_ref(v_eq_2391_);
v___x_2406_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2391_, v_a_2392_, v_a_2396_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; uint8_t v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = lean_unbox(v_a_2407_);
lean_dec(v_a_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_inc_ref(v_eq_2391_);
v___x_2409_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2391_, v_a_2392_, v_a_2396_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; uint8_t v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = lean_unbox(v_a_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___y_2414_; lean_object* v_toGoalState_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2459_; 
v___x_2412_ = lean_st_ref_get(v_a_2392_);
v_toGoalState_2447_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2412_, 1);
lean_dec(v_unused_2460_);
v___x_2449_ = v___x_2412_;
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_toGoalState_2447_);
lean_dec(v___x_2412_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
v___jp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2415_ = l_Lean_Expr_getAppNumArgs(v_a_2389_);
v___x_2416_ = lean_box(0);
lean_inc_ref(v_b_2390_);
lean_inc_ref(v_a_2389_);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v_a_2389_);
lean_ctor_set(v___x_2417_, 1, v_b_2390_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2415_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2416_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = lean_unbox(v_a_2410_);
v___x_2421_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___x_2420_, v___y_2414_, v_eq_2391_, v_a_2389_, v_b_2390_, v___x_2419_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2438_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2438_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2438_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_fst_2426_; 
v_fst_2426_ = lean_ctor_get(v_a_2422_, 0);
lean_inc(v_fst_2426_);
lean_dec(v_a_2422_);
if (lean_obj_tag(v_fst_2426_) == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2432_; 
v___x_2427_ = lean_unsigned_to_nat(2u);
v___x_2428_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
v___x_2429_ = lean_unbox(v_a_2410_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*1, v___x_2429_);
v___x_2430_ = lean_unbox(v_a_2410_);
lean_dec(v_a_2410_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*1 + 1, v___x_2430_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2428_);
v___x_2432_ = v___x_2424_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2428_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v_val_2434_; lean_object* v___x_2436_; 
lean_dec(v_a_2410_);
v_val_2434_ = lean_ctor_get(v_fst_2426_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v_fst_2426_, 1);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_val_2434_);
v___x_2436_ = v___x_2424_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_val_2434_);
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
lean_dec(v_a_2410_);
v_a_2439_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2421_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2421_);
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
v_resetjp_2448_:
{
lean_object* v_split_2451_; lean_object* v_argPosMap_2452_; lean_object* v___x_2454_; 
v_split_2451_ = lean_ctor_get(v_toGoalState_2447_, 15);
lean_inc_ref(v_split_2451_);
lean_dec_ref(v_toGoalState_2447_);
v_argPosMap_2452_ = lean_ctor_get(v_split_2451_, 5);
lean_inc_ref(v_argPosMap_2452_);
lean_dec_ref(v_split_2451_);
lean_inc_ref(v_b_2390_);
lean_inc_ref(v_a_2389_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_b_2390_);
lean_ctor_set(v___x_2449_, 0, v_a_2389_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2389_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_b_2390_);
v___x_2454_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2452_, v___x_2454_);
lean_dec_ref(v___x_2454_);
lean_dec_ref(v_argPosMap_2452_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_box(0);
v___y_2414_ = v___x_2456_;
goto v___jp_2413_;
}
else
{
lean_object* v_val_2457_; 
v_val_2457_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v___x_2455_, 1);
v___y_2414_ = v_val_2457_;
goto v___jp_2413_;
}
}
}
}
else
{
lean_dec(v_a_2410_);
lean_dec_ref(v_eq_2391_);
lean_dec_ref(v_b_2390_);
lean_dec_ref(v_a_2389_);
goto v___jp_2403_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v_eq_2391_);
lean_dec_ref(v_b_2390_);
lean_dec_ref(v_a_2389_);
v_a_2461_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2409_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2409_);
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
lean_dec_ref(v_eq_2391_);
lean_dec_ref(v_b_2390_);
lean_dec_ref(v_a_2389_);
goto v___jp_2403_;
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_eq_2391_);
lean_dec_ref(v_b_2390_);
lean_dec_ref(v_a_2389_);
v_a_2469_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2406_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2406_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
v___jp_2403_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2477_, lean_object* v_b_2478_, lean_object* v_eq_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2477_, v_b_2478_, v_eq_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec(v_a_2480_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2492_, lean_object* v___y_2493_, lean_object* v_eq_2494_, lean_object* v_a_2495_, lean_object* v_b_2496_, lean_object* v_inst_2497_, lean_object* v_a_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2492_, v___y_2493_, v_eq_2494_, v_a_2495_, v_b_2496_, v_a_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2511_ = _args[0];
lean_object* v___y_2512_ = _args[1];
lean_object* v_eq_2513_ = _args[2];
lean_object* v_a_2514_ = _args[3];
lean_object* v_b_2515_ = _args[4];
lean_object* v_inst_2516_ = _args[5];
lean_object* v_a_2517_ = _args[6];
lean_object* v___y_2518_ = _args[7];
lean_object* v___y_2519_ = _args[8];
lean_object* v___y_2520_ = _args[9];
lean_object* v___y_2521_ = _args[10];
lean_object* v___y_2522_ = _args[11];
lean_object* v___y_2523_ = _args[12];
lean_object* v___y_2524_ = _args[13];
lean_object* v___y_2525_ = _args[14];
lean_object* v___y_2526_ = _args[15];
lean_object* v___y_2527_ = _args[16];
lean_object* v___y_2528_ = _args[17];
_start:
{
uint8_t v_a_34972__boxed_2529_; lean_object* v_res_2530_; 
v_a_34972__boxed_2529_ = lean_unbox(v_a_2511_);
v_res_2530_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34972__boxed_2529_, v___y_2512_, v_eq_2513_, v_a_2514_, v_b_2515_, v_inst_2516_, v_a_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec(v___y_2518_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2531_, lean_object* v_m_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2532_, v_a_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2535_, lean_object* v_m_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2535_, v_m_2536_, v_a_2537_);
lean_dec_ref(v_a_2537_);
lean_dec_ref(v_m_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2539_, lean_object* v_a_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2540_, v_x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2543_, lean_object* v_a_2544_, lean_object* v_x_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2543_, v_a_2544_, v_x_2545_);
lean_dec(v_x_2545_);
lean_dec_ref(v_a_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2561_; 
lean_inc_ref(v_imp_2547_);
v___x_2561_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; uint8_t v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = lean_unbox(v_a_2562_);
lean_dec(v_a_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2578_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2578_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2578_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_unbox(v_a_2565_);
lean_dec(v_a_2565_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_box(1);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2570_);
v___x_2572_ = v___x_2567_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_box(0);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2574_);
v___x_2576_ = v___x_2567_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
v_a_2579_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2564_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2564_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_binderType_2587_; lean_object* v_body_2588_; lean_object* v___x_2589_; 
v_binderType_2587_ = lean_ctor_get(v_imp_2547_, 1);
lean_inc_ref_n(v_binderType_2587_, 2);
v_body_2588_ = lean_ctor_get(v_imp_2547_, 2);
lean_inc_ref(v_body_2588_);
lean_dec_ref(v_imp_2547_);
v___x_2589_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2587_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2587_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2629_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2629_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2629_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_unbox(v_a_2593_);
if (v___x_2605_ == 0)
{
uint8_t v___x_2606_; 
v___x_2606_ = l_Lean_Expr_hasLooseBVars(v_body_2588_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
lean_inc_ref(v_body_2588_);
v___x_2607_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2588_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; uint8_t v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = lean_unbox(v_a_2608_);
lean_dec(v_a_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2588_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; uint8_t v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
if (v___x_2612_ == 0)
{
goto v___jp_2597_;
}
else
{
lean_del_object(v___x_2595_);
lean_dec(v_a_2593_);
goto v___jp_2555_;
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_del_object(v___x_2595_);
lean_dec(v_a_2593_);
v_a_2613_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2610_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2610_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_del_object(v___x_2595_);
lean_dec(v_a_2593_);
lean_dec_ref(v_body_2588_);
goto v___jp_2555_;
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_del_object(v___x_2595_);
lean_dec(v_a_2593_);
lean_dec_ref(v_body_2588_);
v_a_2621_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2607_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2607_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_dec_ref(v_body_2588_);
goto v___jp_2597_;
}
}
else
{
lean_del_object(v___x_2595_);
lean_dec(v_a_2593_);
lean_dec_ref(v_body_2588_);
goto v___jp_2558_;
}
v___jp_2597_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; uint8_t v___x_2601_; lean_object* v___x_2603_; 
v___x_2598_ = lean_unsigned_to_nat(2u);
v___x_2599_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
v___x_2600_ = lean_unbox(v_a_2593_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1, v___x_2600_);
v___x_2601_ = lean_unbox(v_a_2593_);
lean_dec(v_a_2593_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1 + 1, v___x_2601_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2599_);
v___x_2603_ = v___x_2595_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2599_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_body_2588_);
v_a_2630_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2592_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2592_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_dec_ref(v_body_2588_);
lean_dec_ref(v_binderType_2587_);
goto v___jp_2558_;
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v_body_2588_);
lean_dec_ref(v_binderType_2587_);
v_a_2638_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2589_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2589_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v_imp_2547_);
v_a_2646_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2561_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2561_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
v___jp_2555_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
return v___x_2557_;
}
v___jp_2558_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2663_, lean_object* v_h_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2663_, v_a_2665_, v_a_2669_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2677_, lean_object* v_h_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2677_, v_h_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec(v_a_2679_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
switch(lean_obj_tag(v_s_2691_))
{
case 0:
{
lean_object* v_e_2703_; lean_object* v___x_2704_; 
v_e_2703_ = lean_ctor_get(v_s_2691_, 0);
lean_inc_ref(v_e_2703_);
lean_dec_ref_known(v_s_2691_, 2);
v___x_2704_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2703_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
return v___x_2704_;
}
case 1:
{
lean_object* v_e_2705_; lean_object* v___x_2706_; 
v_e_2705_ = lean_ctor_get(v_s_2691_, 0);
lean_inc_ref(v_e_2705_);
lean_dec_ref_known(v_s_2691_, 2);
v___x_2706_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2705_, v_a_2692_, v_a_2696_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
return v___x_2706_;
}
default: 
{
lean_object* v_a_2707_; lean_object* v_b_2708_; lean_object* v_eq_2709_; lean_object* v___x_2710_; 
v_a_2707_ = lean_ctor_get(v_s_2691_, 0);
lean_inc_ref(v_a_2707_);
v_b_2708_ = lean_ctor_get(v_s_2691_, 1);
lean_inc_ref(v_b_2708_);
v_eq_2709_ = lean_ctor_get(v_s_2691_, 3);
lean_inc_ref(v_eq_2709_);
lean_dec_ref_known(v_s_2691_, 5);
v___x_2710_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2707_, v_b_2708_, v_eq_2709_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec(v_a_2712_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_obj_tag_nat(v_x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2726_);
lean_dec(v_x_2726_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2728_, lean_object* v_k_2729_){
_start:
{
if (lean_obj_tag(v_t_2728_) == 0)
{
return v_k_2729_;
}
else
{
lean_object* v_c_2730_; lean_object* v_numCases_2731_; uint8_t v_isRec_2732_; uint8_t v_tryPostpone_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_c_2730_ = lean_ctor_get(v_t_2728_, 0);
lean_inc_ref(v_c_2730_);
v_numCases_2731_ = lean_ctor_get(v_t_2728_, 1);
lean_inc(v_numCases_2731_);
v_isRec_2732_ = lean_ctor_get_uint8(v_t_2728_, sizeof(void*)*2);
v_tryPostpone_2733_ = lean_ctor_get_uint8(v_t_2728_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2728_, 2);
v___x_2734_ = lean_box(v_isRec_2732_);
v___x_2735_ = lean_box(v_tryPostpone_2733_);
v___x_2736_ = lean_apply_4(v_k_2729_, v_c_2730_, v_numCases_2731_, v___x_2734_, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2737_, lean_object* v_ctorIdx_2738_, lean_object* v_t_2739_, lean_object* v_h_2740_, lean_object* v_k_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2739_, v_k_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2743_, lean_object* v_ctorIdx_2744_, lean_object* v_t_2745_, lean_object* v_h_2746_, lean_object* v_k_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2743_, v_ctorIdx_2744_, v_t_2745_, v_h_2746_, v_k_2747_);
lean_dec(v_ctorIdx_2744_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2749_, lean_object* v_none_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2749_, v_none_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2752_, lean_object* v_t_2753_, lean_object* v_h_2754_, lean_object* v_none_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2753_, v_none_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2757_, lean_object* v_some_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2757_, v_some_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2760_, lean_object* v_t_2761_, lean_object* v_h_2762_, lean_object* v_some_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2761_, v_some_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2765_, lean_object* v_as_2766_, size_t v_i_2767_, size_t v_stop_2768_){
_start:
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_usize_dec_eq(v_i_2767_, v_stop_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = lean_array_uget_borrowed(v_as_2766_, v_i_2767_);
v___x_2771_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2770_, v_a_2765_);
if (v___x_2771_ == 0)
{
size_t v___x_2772_; size_t v___x_2773_; 
v___x_2772_ = ((size_t)1ULL);
v___x_2773_ = lean_usize_add(v_i_2767_, v___x_2772_);
v_i_2767_ = v___x_2773_;
goto _start;
}
else
{
return v___x_2771_;
}
}
else
{
uint8_t v___x_2775_; 
v___x_2775_ = 0;
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2776_, lean_object* v_as_2777_, lean_object* v_i_2778_, lean_object* v_stop_2779_){
_start:
{
uint64_t v_a_2507__boxed_2780_; size_t v_i_boxed_2781_; size_t v_stop_boxed_2782_; uint8_t v_res_2783_; lean_object* v_r_2784_; 
v_a_2507__boxed_2780_ = lean_unbox_uint64(v_a_2776_);
lean_dec_ref(v_a_2776_);
v_i_boxed_2781_ = lean_unbox_usize(v_i_2778_);
lean_dec(v_i_2778_);
v_stop_boxed_2782_ = lean_unbox_usize(v_stop_2779_);
lean_dec(v_stop_2779_);
v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2780_, v_as_2777_, v_i_boxed_2781_, v_stop_boxed_2782_);
lean_dec_ref(v_as_2777_);
v_r_2784_ = lean_box(v_res_2783_);
return v_r_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2787_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2840_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2840_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2840_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
if (lean_obj_tag(v_a_2797_) == 1)
{
lean_object* v_val_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2799_);
v_val_2801_ = lean_ctor_get(v_a_2797_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v_a_2797_, 1);
v___x_2802_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2826_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2826_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2826_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_array_get_size(v_val_2801_);
v___x_2809_ = lean_nat_dec_lt(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
lean_dec(v_a_2803_);
lean_dec(v_val_2801_);
v___x_2810_ = lean_box(v___x_2809_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2810_);
v___x_2812_ = v___x_2805_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
else
{
if (v___x_2809_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
lean_dec(v_a_2803_);
lean_dec(v_val_2801_);
v___x_2814_ = lean_box(v___x_2809_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2814_);
v___x_2816_ = v___x_2805_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
else
{
size_t v___x_2818_; size_t v___x_2819_; uint64_t v___x_2820_; uint8_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2818_ = ((size_t)0ULL);
v___x_2819_ = lean_usize_of_nat(v___x_2808_);
v___x_2820_ = lean_unbox_uint64(v_a_2803_);
lean_dec(v_a_2803_);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2820_, v_val_2801_, v___x_2818_, v___x_2819_);
lean_dec(v_val_2801_);
v___x_2822_ = lean_box(v___x_2821_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2822_);
v___x_2824_ = v___x_2805_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_val_2801_);
v_a_2827_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2802_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2802_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_dec(v_a_2797_);
v___x_2835_ = 1;
v___x_2836_ = lean_box(v___x_2835_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2836_);
v___x_2838_ = v___x_2799_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_a_2841_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2796_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2796_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_c_2849_);
return v_res_2860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2863_ = l_Lean_stringToMessageData(v___x_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2864_, lean_object* v_c_x3f_2865_, lean_object* v_cs_x27_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
if (lean_obj_tag(v_cs_2864_) == 0)
{
lean_object* v___x_2878_; lean_object* v_toGoalState_2879_; lean_object* v_split_2880_; lean_object* v_mvarId_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2996_; 
v___x_2878_ = lean_st_ref_take(v_a_2867_);
v_toGoalState_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc_ref(v_toGoalState_2879_);
v_split_2880_ = lean_ctor_get(v_toGoalState_2879_, 15);
lean_inc_ref(v_split_2880_);
v_mvarId_2881_ = lean_ctor_get(v___x_2878_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2878_, 0);
lean_dec(v_unused_2997_);
v___x_2883_ = v___x_2878_;
v_isShared_2884_ = v_isSharedCheck_2996_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_mvarId_2881_);
lean_dec(v___x_2878_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2996_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v_nextDeclIdx_2885_; lean_object* v_enodeMap_2886_; lean_object* v_exprs_2887_; lean_object* v_parents_2888_; lean_object* v_congrTable_2889_; lean_object* v_appMap_2890_; lean_object* v_indicesFound_2891_; lean_object* v_toProcess_2892_; lean_object* v_internalizing_2893_; uint8_t v_inconsistent_2894_; lean_object* v_nextIdx_2895_; lean_object* v_newRawFacts_2896_; lean_object* v_facts_2897_; lean_object* v_extThms_2898_; lean_object* v_ematch_2899_; lean_object* v_inj_2900_; lean_object* v_clean_2901_; lean_object* v_sstates_2902_; lean_object* v_goalStack_2903_; uint64_t v_introBase_2904_; lean_object* v_numIntros_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2994_; 
v_nextDeclIdx_2885_ = lean_ctor_get(v_toGoalState_2879_, 0);
v_enodeMap_2886_ = lean_ctor_get(v_toGoalState_2879_, 1);
v_exprs_2887_ = lean_ctor_get(v_toGoalState_2879_, 2);
v_parents_2888_ = lean_ctor_get(v_toGoalState_2879_, 3);
v_congrTable_2889_ = lean_ctor_get(v_toGoalState_2879_, 4);
v_appMap_2890_ = lean_ctor_get(v_toGoalState_2879_, 5);
v_indicesFound_2891_ = lean_ctor_get(v_toGoalState_2879_, 6);
v_toProcess_2892_ = lean_ctor_get(v_toGoalState_2879_, 7);
v_internalizing_2893_ = lean_ctor_get(v_toGoalState_2879_, 8);
v_inconsistent_2894_ = lean_ctor_get_uint8(v_toGoalState_2879_, sizeof(void*)*20 + 8);
v_nextIdx_2895_ = lean_ctor_get(v_toGoalState_2879_, 9);
v_newRawFacts_2896_ = lean_ctor_get(v_toGoalState_2879_, 10);
v_facts_2897_ = lean_ctor_get(v_toGoalState_2879_, 11);
v_extThms_2898_ = lean_ctor_get(v_toGoalState_2879_, 12);
v_ematch_2899_ = lean_ctor_get(v_toGoalState_2879_, 13);
v_inj_2900_ = lean_ctor_get(v_toGoalState_2879_, 14);
v_clean_2901_ = lean_ctor_get(v_toGoalState_2879_, 16);
v_sstates_2902_ = lean_ctor_get(v_toGoalState_2879_, 17);
v_goalStack_2903_ = lean_ctor_get(v_toGoalState_2879_, 18);
v_introBase_2904_ = lean_ctor_get_uint64(v_toGoalState_2879_, sizeof(void*)*20);
v_numIntros_2905_ = lean_ctor_get(v_toGoalState_2879_, 19);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_toGoalState_2879_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v_toGoalState_2879_, 15);
lean_dec(v_unused_2995_);
v___x_2907_ = v_toGoalState_2879_;
v_isShared_2908_ = v_isSharedCheck_2994_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_numIntros_2905_);
lean_inc(v_goalStack_2903_);
lean_inc(v_sstates_2902_);
lean_inc(v_clean_2901_);
lean_inc(v_inj_2900_);
lean_inc(v_ematch_2899_);
lean_inc(v_extThms_2898_);
lean_inc(v_facts_2897_);
lean_inc(v_newRawFacts_2896_);
lean_inc(v_nextIdx_2895_);
lean_inc(v_internalizing_2893_);
lean_inc(v_toProcess_2892_);
lean_inc(v_indicesFound_2891_);
lean_inc(v_appMap_2890_);
lean_inc(v_congrTable_2889_);
lean_inc(v_parents_2888_);
lean_inc(v_exprs_2887_);
lean_inc(v_enodeMap_2886_);
lean_inc(v_nextDeclIdx_2885_);
lean_dec(v_toGoalState_2879_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2994_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_added_2909_; lean_object* v_resolved_2910_; lean_object* v_trace_2911_; lean_object* v_lookaheads_2912_; lean_object* v_argPosMap_2913_; lean_object* v_argsAt_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2992_; 
v_added_2909_ = lean_ctor_get(v_split_2880_, 1);
v_resolved_2910_ = lean_ctor_get(v_split_2880_, 2);
v_trace_2911_ = lean_ctor_get(v_split_2880_, 3);
v_lookaheads_2912_ = lean_ctor_get(v_split_2880_, 4);
v_argPosMap_2913_ = lean_ctor_get(v_split_2880_, 5);
v_argsAt_2914_ = lean_ctor_get(v_split_2880_, 6);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_split_2880_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v_split_2880_, 0);
lean_dec(v_unused_2993_);
v___x_2916_ = v_split_2880_;
v_isShared_2917_ = v_isSharedCheck_2992_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_argsAt_2914_);
lean_inc(v_argPosMap_2913_);
lean_inc(v_lookaheads_2912_);
lean_inc(v_trace_2911_);
lean_inc(v_resolved_2910_);
lean_inc(v_added_2909_);
lean_dec(v_split_2880_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2992_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = l_List_reverse___redArg(v_cs_x27_2866_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_added_2909_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_resolved_2910_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_trace_2911_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_lookaheads_2912_);
lean_ctor_set(v_reuseFailAlloc_2991_, 5, v_argPosMap_2913_);
lean_ctor_set(v_reuseFailAlloc_2991_, 6, v_argsAt_2914_);
v___x_2920_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 15, v___x_2920_);
v___x_2922_ = v___x_2907_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_nextDeclIdx_2885_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_enodeMap_2886_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_exprs_2887_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_parents_2888_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_congrTable_2889_);
lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_appMap_2890_);
lean_ctor_set(v_reuseFailAlloc_2990_, 6, v_indicesFound_2891_);
lean_ctor_set(v_reuseFailAlloc_2990_, 7, v_toProcess_2892_);
lean_ctor_set(v_reuseFailAlloc_2990_, 8, v_internalizing_2893_);
lean_ctor_set(v_reuseFailAlloc_2990_, 9, v_nextIdx_2895_);
lean_ctor_set(v_reuseFailAlloc_2990_, 10, v_newRawFacts_2896_);
lean_ctor_set(v_reuseFailAlloc_2990_, 11, v_facts_2897_);
lean_ctor_set(v_reuseFailAlloc_2990_, 12, v_extThms_2898_);
lean_ctor_set(v_reuseFailAlloc_2990_, 13, v_ematch_2899_);
lean_ctor_set(v_reuseFailAlloc_2990_, 14, v_inj_2900_);
lean_ctor_set(v_reuseFailAlloc_2990_, 15, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2990_, 16, v_clean_2901_);
lean_ctor_set(v_reuseFailAlloc_2990_, 17, v_sstates_2902_);
lean_ctor_set(v_reuseFailAlloc_2990_, 18, v_goalStack_2903_);
lean_ctor_set(v_reuseFailAlloc_2990_, 19, v_numIntros_2905_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*20 + 8, v_inconsistent_2894_);
lean_ctor_set_uint64(v_reuseFailAlloc_2990_, sizeof(void*)*20, v_introBase_2904_);
v___x_2922_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2922_);
v___x_2924_ = v___x_2883_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2922_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_mvarId_2881_);
v___x_2924_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_st_ref_put(v_a_2867_, v___x_2924_);
if (lean_obj_tag(v_c_x3f_2865_) == 1)
{
lean_object* v___x_2926_; lean_object* v_toGoalState_2927_; lean_object* v_ematch_2928_; lean_object* v_mvarId_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2986_; 
v___x_2926_ = lean_st_ref_take(v_a_2867_);
v_toGoalState_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_ref(v_toGoalState_2927_);
v_ematch_2928_ = lean_ctor_get(v_toGoalState_2927_, 13);
lean_inc_ref(v_ematch_2928_);
v_mvarId_2929_ = lean_ctor_get(v___x_2926_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2926_, 0);
lean_dec(v_unused_2987_);
v___x_2931_ = v___x_2926_;
v_isShared_2932_ = v_isSharedCheck_2986_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_mvarId_2929_);
lean_dec(v___x_2926_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2986_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v_nextDeclIdx_2933_; lean_object* v_enodeMap_2934_; lean_object* v_exprs_2935_; lean_object* v_parents_2936_; lean_object* v_congrTable_2937_; lean_object* v_appMap_2938_; lean_object* v_indicesFound_2939_; lean_object* v_toProcess_2940_; lean_object* v_internalizing_2941_; uint8_t v_inconsistent_2942_; lean_object* v_nextIdx_2943_; lean_object* v_newRawFacts_2944_; lean_object* v_facts_2945_; lean_object* v_extThms_2946_; lean_object* v_inj_2947_; lean_object* v_split_2948_; lean_object* v_clean_2949_; lean_object* v_sstates_2950_; lean_object* v_goalStack_2951_; uint64_t v_introBase_2952_; lean_object* v_numIntros_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2984_; 
v_nextDeclIdx_2933_ = lean_ctor_get(v_toGoalState_2927_, 0);
v_enodeMap_2934_ = lean_ctor_get(v_toGoalState_2927_, 1);
v_exprs_2935_ = lean_ctor_get(v_toGoalState_2927_, 2);
v_parents_2936_ = lean_ctor_get(v_toGoalState_2927_, 3);
v_congrTable_2937_ = lean_ctor_get(v_toGoalState_2927_, 4);
v_appMap_2938_ = lean_ctor_get(v_toGoalState_2927_, 5);
v_indicesFound_2939_ = lean_ctor_get(v_toGoalState_2927_, 6);
v_toProcess_2940_ = lean_ctor_get(v_toGoalState_2927_, 7);
v_internalizing_2941_ = lean_ctor_get(v_toGoalState_2927_, 8);
v_inconsistent_2942_ = lean_ctor_get_uint8(v_toGoalState_2927_, sizeof(void*)*20 + 8);
v_nextIdx_2943_ = lean_ctor_get(v_toGoalState_2927_, 9);
v_newRawFacts_2944_ = lean_ctor_get(v_toGoalState_2927_, 10);
v_facts_2945_ = lean_ctor_get(v_toGoalState_2927_, 11);
v_extThms_2946_ = lean_ctor_get(v_toGoalState_2927_, 12);
v_inj_2947_ = lean_ctor_get(v_toGoalState_2927_, 14);
v_split_2948_ = lean_ctor_get(v_toGoalState_2927_, 15);
v_clean_2949_ = lean_ctor_get(v_toGoalState_2927_, 16);
v_sstates_2950_ = lean_ctor_get(v_toGoalState_2927_, 17);
v_goalStack_2951_ = lean_ctor_get(v_toGoalState_2927_, 18);
v_introBase_2952_ = lean_ctor_get_uint64(v_toGoalState_2927_, sizeof(void*)*20);
v_numIntros_2953_ = lean_ctor_get(v_toGoalState_2927_, 19);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_toGoalState_2927_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_toGoalState_2927_, 13);
lean_dec(v_unused_2985_);
v___x_2955_ = v_toGoalState_2927_;
v_isShared_2956_ = v_isSharedCheck_2984_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_numIntros_2953_);
lean_inc(v_goalStack_2951_);
lean_inc(v_sstates_2950_);
lean_inc(v_clean_2949_);
lean_inc(v_split_2948_);
lean_inc(v_inj_2947_);
lean_inc(v_extThms_2946_);
lean_inc(v_facts_2945_);
lean_inc(v_newRawFacts_2944_);
lean_inc(v_nextIdx_2943_);
lean_inc(v_internalizing_2941_);
lean_inc(v_toProcess_2940_);
lean_inc(v_indicesFound_2939_);
lean_inc(v_appMap_2938_);
lean_inc(v_congrTable_2937_);
lean_inc(v_parents_2936_);
lean_inc(v_exprs_2935_);
lean_inc(v_enodeMap_2934_);
lean_inc(v_nextDeclIdx_2933_);
lean_dec(v_toGoalState_2927_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2984_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_thmMap_2957_; lean_object* v_gmt_2958_; lean_object* v_thms_2959_; lean_object* v_newThms_2960_; lean_object* v_numInstances_2961_; lean_object* v_numDelayedInstances_2962_; lean_object* v_preInstances_2963_; lean_object* v_nextThmIdx_2964_; lean_object* v_matchEqNames_2965_; lean_object* v_delayedThmInsts_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2982_; 
v_thmMap_2957_ = lean_ctor_get(v_ematch_2928_, 0);
v_gmt_2958_ = lean_ctor_get(v_ematch_2928_, 1);
v_thms_2959_ = lean_ctor_get(v_ematch_2928_, 2);
v_newThms_2960_ = lean_ctor_get(v_ematch_2928_, 3);
v_numInstances_2961_ = lean_ctor_get(v_ematch_2928_, 4);
v_numDelayedInstances_2962_ = lean_ctor_get(v_ematch_2928_, 5);
v_preInstances_2963_ = lean_ctor_get(v_ematch_2928_, 7);
v_nextThmIdx_2964_ = lean_ctor_get(v_ematch_2928_, 8);
v_matchEqNames_2965_ = lean_ctor_get(v_ematch_2928_, 9);
v_delayedThmInsts_2966_ = lean_ctor_get(v_ematch_2928_, 10);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_ematch_2928_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_ematch_2928_, 6);
lean_dec(v_unused_2983_);
v___x_2968_ = v_ematch_2928_;
v_isShared_2969_ = v_isSharedCheck_2982_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_delayedThmInsts_2966_);
lean_inc(v_matchEqNames_2965_);
lean_inc(v_nextThmIdx_2964_);
lean_inc(v_preInstances_2963_);
lean_inc(v_numDelayedInstances_2962_);
lean_inc(v_numInstances_2961_);
lean_inc(v_newThms_2960_);
lean_inc(v_thms_2959_);
lean_inc(v_gmt_2958_);
lean_inc(v_thmMap_2957_);
lean_dec(v_ematch_2928_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2982_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2970_ = lean_unsigned_to_nat(0u);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 6, v___x_2970_);
v___x_2972_ = v___x_2968_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_thmMap_2957_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_gmt_2958_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_thms_2959_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_newThms_2960_);
lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_numInstances_2961_);
lean_ctor_set(v_reuseFailAlloc_2981_, 5, v_numDelayedInstances_2962_);
lean_ctor_set(v_reuseFailAlloc_2981_, 6, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2981_, 7, v_preInstances_2963_);
lean_ctor_set(v_reuseFailAlloc_2981_, 8, v_nextThmIdx_2964_);
lean_ctor_set(v_reuseFailAlloc_2981_, 9, v_matchEqNames_2965_);
lean_ctor_set(v_reuseFailAlloc_2981_, 10, v_delayedThmInsts_2966_);
v___x_2972_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 13, v___x_2972_);
v___x_2974_ = v___x_2955_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_nextDeclIdx_2933_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_enodeMap_2934_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_exprs_2935_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_parents_2936_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_congrTable_2937_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v_appMap_2938_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v_indicesFound_2939_);
lean_ctor_set(v_reuseFailAlloc_2980_, 7, v_toProcess_2940_);
lean_ctor_set(v_reuseFailAlloc_2980_, 8, v_internalizing_2941_);
lean_ctor_set(v_reuseFailAlloc_2980_, 9, v_nextIdx_2943_);
lean_ctor_set(v_reuseFailAlloc_2980_, 10, v_newRawFacts_2944_);
lean_ctor_set(v_reuseFailAlloc_2980_, 11, v_facts_2945_);
lean_ctor_set(v_reuseFailAlloc_2980_, 12, v_extThms_2946_);
lean_ctor_set(v_reuseFailAlloc_2980_, 13, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2980_, 14, v_inj_2947_);
lean_ctor_set(v_reuseFailAlloc_2980_, 15, v_split_2948_);
lean_ctor_set(v_reuseFailAlloc_2980_, 16, v_clean_2949_);
lean_ctor_set(v_reuseFailAlloc_2980_, 17, v_sstates_2950_);
lean_ctor_set(v_reuseFailAlloc_2980_, 18, v_goalStack_2951_);
lean_ctor_set(v_reuseFailAlloc_2980_, 19, v_numIntros_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*20 + 8, v_inconsistent_2942_);
lean_ctor_set_uint64(v_reuseFailAlloc_2980_, sizeof(void*)*20, v_introBase_2952_);
v___x_2974_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2974_);
v___x_2976_ = v___x_2931_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_mvarId_2929_);
v___x_2976_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_st_ref_put(v_a_2867_, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_c_x3f_2865_);
return v___x_2978_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_c_x3f_2865_);
return v___x_2988_;
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
lean_object* v_head_2998_; lean_object* v_tail_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3219_; 
v_head_2998_ = lean_ctor_get(v_cs_2864_, 0);
v_tail_2999_ = lean_ctor_get(v_cs_2864_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_cs_2864_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3001_ = v_cs_2864_;
v_isShared_3002_ = v_isSharedCheck_3219_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_tail_2999_);
lean_inc(v_head_2998_);
lean_dec(v_cs_2864_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3219_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; uint8_t v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3048_; uint8_t v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; uint8_t v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; uint8_t v___y_3104_; uint8_t v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; uint8_t v___y_3108_; lean_object* v___x_3111_; 
v___x_3111_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2998_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; uint8_t v___x_3113_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = lean_unbox(v_a_3112_);
lean_dec(v_a_3112_);
if (v___x_3113_ == 0)
{
lean_del_object(v___x_3001_);
lean_dec(v_head_2998_);
v_cs_2864_ = v_tail_2999_;
goto _start;
}
else
{
lean_object* v_toCold_3115_; lean_object* v_options_3116_; lean_object* v_inheritedTraceOptions_3117_; uint8_t v_hasTrace_3118_; uint8_t v___x_3119_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3133_; uint8_t v___y_3134_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; 
v_toCold_3115_ = lean_ctor_get(v_a_2875_, 0);
v_options_3116_ = lean_ctor_get(v_toCold_3115_, 2);
v_inheritedTraceOptions_3117_ = lean_ctor_get(v_toCold_3115_, 11);
v_hasTrace_3118_ = lean_ctor_get_uint8(v_options_3116_, sizeof(void*)*1);
v___x_3119_ = 0;
if (v_hasTrace_3118_ == 0)
{
v___y_3145_ = v_a_2867_;
v___y_3146_ = v_a_2868_;
v___y_3147_ = v_a_2869_;
v___y_3148_ = v_a_2870_;
v___y_3149_ = v_a_2871_;
v___y_3150_ = v_a_2872_;
v___y_3151_ = v_a_2873_;
v___y_3152_ = v_a_2874_;
v___y_3153_ = v_a_2875_;
v___y_3154_ = v_a_2876_;
goto v___jp_3144_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3117_, v_options_3116_, v___x_3187_);
if (v___x_3188_ == 0)
{
v___y_3145_ = v_a_2867_;
v___y_3146_ = v_a_2868_;
v___y_3147_ = v_a_2869_;
v___y_3148_ = v_a_2870_;
v___y_3149_ = v_a_2871_;
v___y_3150_ = v_a_2872_;
v___y_3151_ = v_a_2873_;
v___y_3152_ = v_a_2874_;
v___y_3153_ = v_a_2875_;
v___y_3154_ = v_a_2876_;
goto v___jp_3144_;
}
else
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Meta_Grind_updateLastTag(v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_dec_ref_known(v___x_3189_, 1);
v___x_3190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3191_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2998_);
v___x_3192_ = l_Lean_MessageData_ofExpr(v___x_3191_);
v___x_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3190_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3186_, v___x_3193_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_dec_ref_known(v___x_3194_, 1);
v___y_3145_ = v_a_2867_;
v___y_3146_ = v_a_2868_;
v___y_3147_ = v_a_2869_;
v___y_3148_ = v_a_2870_;
v___y_3149_ = v_a_2871_;
v___y_3150_ = v_a_2872_;
v___y_3151_ = v_a_2873_;
v___y_3152_ = v_a_2874_;
v___y_3153_ = v_a_2875_;
v___y_3154_ = v_a_2876_;
goto v___jp_3144_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
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
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3203_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3189_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3189_);
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
}
v___jp_3120_:
{
if (lean_obj_tag(v_c_x3f_2865_) == 0)
{
lean_object* v___x_3135_; 
lean_del_object(v___x_3001_);
v___x_3135_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3135_, 0, v_head_2998_);
lean_ctor_set(v___x_3135_, 1, v___y_3131_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*2, v___y_3129_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*2 + 1, v___y_3132_);
v_cs_2864_ = v_tail_2999_;
v_c_x3f_2865_ = v___x_3135_;
v_a_2867_ = v___y_3126_;
v_a_2868_ = v___y_3124_;
v_a_2869_ = v___y_3123_;
v_a_2870_ = v___y_3133_;
v_a_2871_ = v___y_3125_;
v_a_2872_ = v___y_3128_;
v_a_2873_ = v___y_3127_;
v_a_2874_ = v___y_3122_;
v_a_2875_ = v___y_3121_;
v_a_2876_ = v___y_3130_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3137_; 
v_tryPostpone_3137_ = lean_ctor_get_uint8(v_c_x3f_2865_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3137_ == 0)
{
if (v___y_3132_ == 0)
{
lean_object* v_c_3138_; lean_object* v_numCases_3139_; 
v_c_3138_ = lean_ctor_get(v_c_x3f_2865_, 0);
v_numCases_3139_ = lean_ctor_get(v_c_x3f_2865_, 1);
lean_inc_ref(v_c_3138_);
lean_inc(v_numCases_3139_);
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___y_3125_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v_numCases_3139_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v___y_3127_;
v___y_3101_ = v_c_3138_;
v___y_3102_ = v___y_3128_;
v___y_3103_ = v___y_3130_;
v___y_3104_ = v___y_3129_;
v___y_3105_ = v___y_3132_;
v___y_3106_ = v___y_3131_;
v___y_3107_ = v___y_3133_;
v___y_3108_ = v___x_3119_;
goto v___jp_3092_;
}
else
{
lean_dec(v___y_3131_);
v___y_3004_ = v___y_3121_;
v___y_3005_ = v___y_3126_;
v___y_3006_ = v___y_3127_;
v___y_3007_ = v___y_3128_;
v___y_3008_ = v___y_3122_;
v___y_3009_ = v___y_3130_;
v___y_3010_ = v___y_3123_;
v___y_3011_ = v___y_3125_;
v___y_3012_ = v___y_3124_;
v___y_3013_ = v___y_3133_;
goto v___jp_3003_;
}
}
else
{
if (v___y_3132_ == 0)
{
lean_object* v_c_3140_; 
lean_del_object(v___x_3001_);
v_c_3140_ = lean_ctor_get(v_c_x3f_2865_, 0);
lean_inc_ref(v_c_3140_);
lean_dec_ref_known(v_c_x3f_2865_, 2);
v___y_3019_ = v___y_3121_;
v___y_3020_ = v___y_3122_;
v___y_3021_ = v___y_3123_;
v___y_3022_ = v___y_3124_;
v___y_3023_ = v___y_3125_;
v___y_3024_ = v___y_3126_;
v___y_3025_ = v___y_3127_;
v___y_3026_ = v_c_3140_;
v___y_3027_ = v___y_3128_;
v___y_3028_ = v___y_3130_;
v___y_3029_ = v___y_3129_;
v___y_3030_ = v___y_3131_;
v___y_3031_ = v___y_3132_;
v___y_3032_ = v___y_3133_;
goto v___jp_3018_;
}
else
{
if (v___y_3134_ == 0)
{
lean_object* v_c_3141_; lean_object* v_numCases_3142_; 
v_c_3141_ = lean_ctor_get(v_c_x3f_2865_, 0);
v_numCases_3142_ = lean_ctor_get(v_c_x3f_2865_, 1);
lean_inc_ref(v_c_3141_);
lean_inc(v_numCases_3142_);
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___y_3125_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v_numCases_3142_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v___y_3127_;
v___y_3101_ = v_c_3141_;
v___y_3102_ = v___y_3128_;
v___y_3103_ = v___y_3130_;
v___y_3104_ = v___y_3129_;
v___y_3105_ = v___y_3132_;
v___y_3106_ = v___y_3131_;
v___y_3107_ = v___y_3133_;
v___y_3108_ = v___y_3134_;
goto v___jp_3092_;
}
else
{
lean_object* v_c_3143_; 
lean_del_object(v___x_3001_);
v_c_3143_ = lean_ctor_get(v_c_x3f_2865_, 0);
lean_inc_ref(v_c_3143_);
lean_dec_ref_known(v_c_x3f_2865_, 2);
v___y_3019_ = v___y_3121_;
v___y_3020_ = v___y_3122_;
v___y_3021_ = v___y_3123_;
v___y_3022_ = v___y_3124_;
v___y_3023_ = v___y_3125_;
v___y_3024_ = v___y_3126_;
v___y_3025_ = v___y_3127_;
v___y_3026_ = v_c_3143_;
v___y_3027_ = v___y_3128_;
v___y_3028_ = v___y_3130_;
v___y_3029_ = v___y_3129_;
v___y_3030_ = v___y_3131_;
v___y_3031_ = v___y_3132_;
v___y_3032_ = v___y_3133_;
goto v___jp_3018_;
}
}
}
}
}
v___jp_3144_:
{
lean_object* v___x_3155_; 
lean_inc(v_head_2998_);
v___x_3155_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2998_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
switch(lean_obj_tag(v_a_3156_))
{
case 0:
{
lean_del_object(v___x_3001_);
lean_dec(v_head_2998_);
v_cs_2864_ = v_tail_2999_;
v_a_2867_ = v___y_3145_;
v_a_2868_ = v___y_3146_;
v_a_2869_ = v___y_3147_;
v_a_2870_ = v___y_3148_;
v_a_2871_ = v___y_3149_;
v_a_2872_ = v___y_3150_;
v_a_2873_ = v___y_3151_;
v_a_2874_ = v___y_3152_;
v_a_2875_ = v___y_3153_;
v_a_2876_ = v___y_3154_;
goto _start;
}
case 1:
{
lean_object* v___x_3158_; 
lean_del_object(v___x_3001_);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_head_2998_);
lean_ctor_set(v___x_3158_, 1, v_cs_x27_2866_);
v_cs_2864_ = v_tail_2999_;
v_cs_x27_2866_ = v___x_3158_;
v_a_2867_ = v___y_3145_;
v_a_2868_ = v___y_3146_;
v_a_2869_ = v___y_3147_;
v_a_2870_ = v___y_3148_;
v_a_2871_ = v___y_3149_;
v_a_2872_ = v___y_3150_;
v_a_2873_ = v___y_3151_;
v_a_2874_ = v___y_3152_;
v_a_2875_ = v___y_3153_;
v_a_2876_ = v___y_3154_;
goto _start;
}
default: 
{
lean_object* v_numCases_3160_; uint8_t v_isRec_3161_; uint8_t v_tryPostpone_3162_; lean_object* v___x_3163_; 
v_numCases_3160_ = lean_ctor_get(v_a_3156_, 0);
lean_inc(v_numCases_3160_);
v_isRec_3161_ = lean_ctor_get_uint8(v_a_3156_, sizeof(void*)*1);
v_tryPostpone_3162_ = lean_ctor_get_uint8(v_a_3156_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3156_, 1);
v___x_3163_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3147_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; uint8_t v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = lean_unbox(v_a_3164_);
lean_dec(v_a_3164_);
if (v___x_3165_ == 0)
{
v___y_3121_ = v___y_3153_;
v___y_3122_ = v___y_3152_;
v___y_3123_ = v___y_3147_;
v___y_3124_ = v___y_3146_;
v___y_3125_ = v___y_3149_;
v___y_3126_ = v___y_3145_;
v___y_3127_ = v___y_3151_;
v___y_3128_ = v___y_3150_;
v___y_3129_ = v_isRec_3161_;
v___y_3130_ = v___y_3154_;
v___y_3131_ = v_numCases_3160_;
v___y_3132_ = v_tryPostpone_3162_;
v___y_3133_ = v___y_3148_;
v___y_3134_ = v___x_3119_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = lean_unsigned_to_nat(1u);
v___x_3167_ = lean_nat_dec_lt(v___x_3166_, v_numCases_3160_);
if (v___x_3167_ == 0)
{
v___y_3121_ = v___y_3153_;
v___y_3122_ = v___y_3152_;
v___y_3123_ = v___y_3147_;
v___y_3124_ = v___y_3146_;
v___y_3125_ = v___y_3149_;
v___y_3126_ = v___y_3145_;
v___y_3127_ = v___y_3151_;
v___y_3128_ = v___y_3150_;
v___y_3129_ = v_isRec_3161_;
v___y_3130_ = v___y_3154_;
v___y_3131_ = v_numCases_3160_;
v___y_3132_ = v_tryPostpone_3162_;
v___y_3133_ = v___y_3148_;
v___y_3134_ = v___x_3167_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3168_; 
lean_dec(v_numCases_3160_);
lean_del_object(v___x_3001_);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_head_2998_);
lean_ctor_set(v___x_3168_, 1, v_cs_x27_2866_);
v_cs_2864_ = v_tail_2999_;
v_cs_x27_2866_ = v___x_3168_;
v_a_2867_ = v___y_3145_;
v_a_2868_ = v___y_3146_;
v_a_2869_ = v___y_3147_;
v_a_2870_ = v___y_3148_;
v_a_2871_ = v___y_3149_;
v_a_2872_ = v___y_3150_;
v_a_2873_ = v___y_3151_;
v_a_2874_ = v___y_3152_;
v_a_2875_ = v___y_3153_;
v_a_2876_ = v___y_3154_;
goto _start;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_numCases_3160_);
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3170_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3163_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3163_);
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
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3178_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3155_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3155_);
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
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3211_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3111_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3111_);
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
v___jp_3003_:
{
lean_object* v___x_3015_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v_cs_x27_2866_);
v___x_3015_ = v___x_3001_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_head_2998_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_cs_x27_2866_);
v___x_3015_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
v_cs_2864_ = v_tail_2999_;
v_cs_x27_2866_ = v___x_3015_;
v_a_2867_ = v___y_3005_;
v_a_2868_ = v___y_3012_;
v_a_2869_ = v___y_3010_;
v_a_2870_ = v___y_3013_;
v_a_2871_ = v___y_3011_;
v_a_2872_ = v___y_3007_;
v_a_2873_ = v___y_3006_;
v_a_2874_ = v___y_3008_;
v_a_2875_ = v___y_3004_;
v_a_2876_ = v___y_3009_;
goto _start;
}
}
v___jp_3018_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3033_, 0, v_head_2998_);
lean_ctor_set(v___x_3033_, 1, v___y_3030_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*2, v___y_3029_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*2 + 1, v___y_3031_);
v___x_3034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___y_3026_);
lean_ctor_set(v___x_3034_, 1, v_cs_x27_2866_);
v_cs_2864_ = v_tail_2999_;
v_c_x3f_2865_ = v___x_3033_;
v_cs_x27_2866_ = v___x_3034_;
v_a_2867_ = v___y_3024_;
v_a_2868_ = v___y_3022_;
v_a_2869_ = v___y_3021_;
v_a_2870_ = v___y_3032_;
v_a_2871_ = v___y_3023_;
v_a_2872_ = v___y_3027_;
v_a_2873_ = v___y_3025_;
v_a_2874_ = v___y_3020_;
v_a_2875_ = v___y_3019_;
v_a_2876_ = v___y_3028_;
goto _start;
}
v___jp_3036_:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2998_, v___y_3043_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3045_, v___y_3043_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; uint8_t v___x_3056_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3056_ = lean_nat_dec_lt(v_a_3053_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec(v_a_3053_);
if (v___x_3056_ == 0)
{
uint8_t v___x_3057_; 
v___x_3057_ = lean_nat_dec_lt(v___y_3050_, v___y_3042_);
lean_dec(v___y_3042_);
if (v___x_3057_ == 0)
{
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3045_);
v___y_3004_ = v___y_3037_;
v___y_3005_ = v___y_3043_;
v___y_3006_ = v___y_3044_;
v___y_3007_ = v___y_3046_;
v___y_3008_ = v___y_3038_;
v___y_3009_ = v___y_3048_;
v___y_3010_ = v___y_3039_;
v___y_3011_ = v___y_3040_;
v___y_3012_ = v___y_3041_;
v___y_3013_ = v___y_3051_;
goto v___jp_3003_;
}
else
{
lean_del_object(v___x_3001_);
lean_dec(v_c_x3f_2865_);
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3039_;
v___y_3022_ = v___y_3041_;
v___y_3023_ = v___y_3040_;
v___y_3024_ = v___y_3043_;
v___y_3025_ = v___y_3044_;
v___y_3026_ = v___y_3045_;
v___y_3027_ = v___y_3046_;
v___y_3028_ = v___y_3048_;
v___y_3029_ = v___y_3047_;
v___y_3030_ = v___y_3050_;
v___y_3031_ = v___y_3049_;
v___y_3032_ = v___y_3051_;
goto v___jp_3018_;
}
}
else
{
lean_dec(v___y_3042_);
lean_del_object(v___x_3001_);
lean_dec(v_c_x3f_2865_);
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3039_;
v___y_3022_ = v___y_3041_;
v___y_3023_ = v___y_3040_;
v___y_3024_ = v___y_3043_;
v___y_3025_ = v___y_3044_;
v___y_3026_ = v___y_3045_;
v___y_3027_ = v___y_3046_;
v___y_3028_ = v___y_3048_;
v___y_3029_ = v___y_3047_;
v___y_3030_ = v___y_3050_;
v___y_3031_ = v___y_3049_;
v___y_3032_ = v___y_3051_;
goto v___jp_3018_;
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_a_3053_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3042_);
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3058_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3054_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3054_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3042_);
lean_del_object(v___x_3001_);
lean_dec(v_tail_2999_);
lean_dec(v_head_2998_);
lean_dec(v_cs_x27_2866_);
lean_dec(v_c_x3f_2865_);
v_a_3066_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3052_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3052_);
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
v___jp_3074_:
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = lean_unsigned_to_nat(1u);
v___x_3091_ = lean_nat_dec_lt(v___x_3090_, v___y_3080_);
if (v___x_3091_ == 0)
{
v___y_3037_ = v___y_3075_;
v___y_3038_ = v___y_3076_;
v___y_3039_ = v___y_3077_;
v___y_3040_ = v___y_3078_;
v___y_3041_ = v___y_3079_;
v___y_3042_ = v___y_3080_;
v___y_3043_ = v___y_3081_;
v___y_3044_ = v___y_3082_;
v___y_3045_ = v___y_3083_;
v___y_3046_ = v___y_3084_;
v___y_3047_ = v___y_3085_;
v___y_3048_ = v___y_3086_;
v___y_3049_ = v___y_3088_;
v___y_3050_ = v___y_3087_;
v___y_3051_ = v___y_3089_;
goto v___jp_3036_;
}
else
{
lean_dec(v___y_3080_);
lean_del_object(v___x_3001_);
lean_dec(v_c_x3f_2865_);
v___y_3019_ = v___y_3075_;
v___y_3020_ = v___y_3076_;
v___y_3021_ = v___y_3077_;
v___y_3022_ = v___y_3079_;
v___y_3023_ = v___y_3078_;
v___y_3024_ = v___y_3081_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_3084_;
v___y_3028_ = v___y_3086_;
v___y_3029_ = v___y_3085_;
v___y_3030_ = v___y_3087_;
v___y_3031_ = v___y_3088_;
v___y_3032_ = v___y_3089_;
goto v___jp_3018_;
}
}
v___jp_3092_:
{
lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3109_ = lean_unsigned_to_nat(1u);
v___x_3110_ = lean_nat_dec_eq(v___y_3106_, v___x_3109_);
if (v___x_3110_ == 0)
{
v___y_3037_ = v___y_3093_;
v___y_3038_ = v___y_3094_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3097_;
v___y_3042_ = v___y_3098_;
v___y_3043_ = v___y_3099_;
v___y_3044_ = v___y_3100_;
v___y_3045_ = v___y_3101_;
v___y_3046_ = v___y_3102_;
v___y_3047_ = v___y_3104_;
v___y_3048_ = v___y_3103_;
v___y_3049_ = v___y_3105_;
v___y_3050_ = v___y_3106_;
v___y_3051_ = v___y_3107_;
goto v___jp_3036_;
}
else
{
if (v___y_3104_ == 0)
{
v___y_3075_ = v___y_3093_;
v___y_3076_ = v___y_3094_;
v___y_3077_ = v___y_3095_;
v___y_3078_ = v___y_3096_;
v___y_3079_ = v___y_3097_;
v___y_3080_ = v___y_3098_;
v___y_3081_ = v___y_3099_;
v___y_3082_ = v___y_3100_;
v___y_3083_ = v___y_3101_;
v___y_3084_ = v___y_3102_;
v___y_3085_ = v___y_3104_;
v___y_3086_ = v___y_3103_;
v___y_3087_ = v___y_3106_;
v___y_3088_ = v___y_3105_;
v___y_3089_ = v___y_3107_;
goto v___jp_3074_;
}
else
{
if (v___y_3108_ == 0)
{
v___y_3037_ = v___y_3093_;
v___y_3038_ = v___y_3094_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3097_;
v___y_3042_ = v___y_3098_;
v___y_3043_ = v___y_3099_;
v___y_3044_ = v___y_3100_;
v___y_3045_ = v___y_3101_;
v___y_3046_ = v___y_3102_;
v___y_3047_ = v___y_3104_;
v___y_3048_ = v___y_3103_;
v___y_3049_ = v___y_3105_;
v___y_3050_ = v___y_3106_;
v___y_3051_ = v___y_3107_;
goto v___jp_3036_;
}
else
{
v___y_3075_ = v___y_3093_;
v___y_3076_ = v___y_3094_;
v___y_3077_ = v___y_3095_;
v___y_3078_ = v___y_3096_;
v___y_3079_ = v___y_3097_;
v___y_3080_ = v___y_3098_;
v___y_3081_ = v___y_3099_;
v___y_3082_ = v___y_3100_;
v___y_3083_ = v___y_3101_;
v___y_3084_ = v___y_3102_;
v___y_3085_ = v___y_3104_;
v___y_3086_ = v___y_3103_;
v___y_3087_ = v___y_3106_;
v___y_3088_ = v___y_3105_;
v___y_3089_ = v___y_3107_;
goto v___jp_3074_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3220_, lean_object* v_c_x3f_3221_, lean_object* v_cs_x27_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3220_, v_c_x3f_3221_, v_cs_x27_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec(v_a_3223_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3235_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3282_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3282_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3282_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
uint8_t v___x_3251_; 
v___x_3251_ = lean_unbox(v_a_3247_);
lean_dec(v_a_3247_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; 
lean_del_object(v___x_3249_);
v___x_3252_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3269_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3269_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3269_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_unbox(v_a_3253_);
lean_dec(v_a_3253_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v_toGoalState_3259_; lean_object* v_split_3260_; lean_object* v_candidates_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_del_object(v___x_3255_);
v___x_3258_ = lean_st_ref_get(v_a_3235_);
v_toGoalState_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_ref(v_toGoalState_3259_);
lean_dec(v___x_3258_);
v_split_3260_ = lean_ctor_get(v_toGoalState_3259_, 15);
lean_inc_ref(v_split_3260_);
lean_dec_ref(v_toGoalState_3259_);
v_candidates_3261_ = lean_ctor_get(v_split_3260_, 0);
lean_inc(v_candidates_3261_);
lean_dec_ref(v_split_3260_);
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_box(0);
v___x_3264_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3261_, v___x_3262_, v___x_3263_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_box(0);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3265_);
v___x_3267_ = v___x_3255_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
v_a_3270_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3252_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3252_);
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
lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3278_ = lean_box(0);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3278_);
v___x_3280_ = v___x_3249_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
v_a_3283_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3246_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3246_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec(v_a_3291_);
return v_res_3302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_box(0);
v___x_3311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3312_ = l_Lean_mkConst(v___x_3311_, v___x_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3313_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3315_ = l_Lean_Expr_app___override(v___x_3314_, v_c_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3323_ = l_Lean_mkConst(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_box(0);
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4));
v___x_3331_ = l_Lean_mkConst(v___x_3330_, v___x_3329_);
return v___x_3331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7));
v___x_3339_ = l_Lean_mkConst(v___x_3338_, v___x_3337_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___x_3401_; 
lean_inc_ref(v_c_3340_);
v___x_3401_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3340_, v_a_3348_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3474_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3474_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3474_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = l_Lean_Expr_cleanupAnnotations(v_a_3402_);
lean_dec(v_a_3402_);
v___x_3407_ = l_Lean_Expr_isApp(v___x_3406_);
if (v___x_3407_ == 0)
{
lean_dec_ref(v___x_3406_);
lean_del_object(v___x_3404_);
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
v___y_3370_ = v_a_3350_;
goto v___jp_3360_;
}
else
{
lean_object* v_arg_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v_arg_3408_ = lean_ctor_get(v___x_3406_, 1);
lean_inc_ref(v_arg_3408_);
v___x_3409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3406_);
lean_dec_ref(v___x_3406_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3411_ = l_Lean_Expr_isConstOf(v___x_3409_, v___x_3410_);
if (v___x_3411_ == 0)
{
uint8_t v___x_3412_; 
v___x_3412_ = l_Lean_Expr_isApp(v___x_3409_);
if (v___x_3412_ == 0)
{
lean_dec_ref(v___x_3409_);
lean_dec_ref(v_arg_3408_);
lean_del_object(v___x_3404_);
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
v___y_3370_ = v_a_3350_;
goto v___jp_3360_;
}
else
{
lean_object* v_arg_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v_arg_3413_ = lean_ctor_get(v___x_3409_, 1);
lean_inc_ref(v_arg_3413_);
v___x_3414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3409_);
lean_dec_ref(v___x_3409_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_3416_ = l_Lean_Expr_isConstOf(v___x_3414_, v___x_3415_);
if (v___x_3416_ == 0)
{
uint8_t v___x_3417_; 
v___x_3417_ = l_Lean_Expr_isApp(v___x_3414_);
if (v___x_3417_ == 0)
{
lean_dec_ref(v___x_3414_);
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
lean_del_object(v___x_3404_);
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
v___y_3370_ = v_a_3350_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3414_);
lean_dec_ref(v___x_3414_);
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20));
v___x_3420_ = l_Lean_Expr_isConstOf(v___x_3418_, v___x_3419_);
lean_dec_ref(v___x_3418_);
if (v___x_3420_ == 0)
{
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
lean_del_object(v___x_3404_);
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
v___y_3370_ = v_a_3350_;
goto v___jp_3360_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3340_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
v___x_3422_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3340_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3422_);
v___x_3424_ = v___x_3404_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
lean_object* v___x_3426_; 
lean_del_object(v___x_3404_);
lean_inc_ref(v_c_3340_);
v___x_3426_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3340_, v_a_3341_, v_a_3345_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; uint8_t v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v___x_3428_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3439_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3439_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3439_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2);
v___x_3435_ = l_Lean_mkApp3(v___x_3434_, v_arg_3413_, v_arg_3408_, v_a_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3435_);
v___x_3437_ = v___x_3432_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
else
{
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
return v___x_3429_;
}
}
else
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3450_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5);
v___x_3446_ = l_Lean_mkApp3(v___x_3445_, v_arg_3413_, v_arg_3408_, v_a_3441_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3446_);
v___x_3448_ = v___x_3443_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
else
{
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_c_3340_);
v_a_3451_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3426_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3426_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3459_; 
lean_dec_ref(v___x_3414_);
lean_del_object(v___x_3404_);
v___x_3459_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3469_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3469_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3469_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8);
v___x_3465_ = l_Lean_mkApp3(v___x_3464_, v_arg_3413_, v_arg_3408_, v_a_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v___x_3465_);
v___x_3467_ = v___x_3462_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_dec_ref(v_arg_3413_);
lean_dec_ref(v_arg_3408_);
return v___x_3459_;
}
}
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_dec_ref(v___x_3409_);
lean_dec_ref(v_c_3340_);
v___x_3470_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3408_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3470_);
v___x_3472_ = v___x_3404_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3340_);
return v___x_3401_;
}
v___jp_3352_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = l_Lean_Expr_getAppNumArgs(v_c_3340_);
v___x_3355_ = lean_nat_sub(v___x_3354_, v___x_3353_);
lean_dec(v___x_3354_);
v___x_3356_ = lean_nat_sub(v___x_3355_, v___x_3353_);
lean_dec(v___x_3355_);
v___x_3357_ = l_Lean_Expr_getRevArg_x21(v_c_3340_, v___x_3356_);
lean_dec_ref(v_c_3340_);
v___x_3358_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3357_);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
v___jp_3360_:
{
uint8_t v___x_3371_; 
v___x_3371_ = l_Lean_Meta_Grind_isIte(v_c_3340_);
if (v___x_3371_ == 0)
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_Meta_Grind_isDIte(v_c_3340_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; 
lean_inc_ref(v_c_3340_);
v___x_3373_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3340_, v___y_3361_, v___y_3365_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3392_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3392_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3392_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_unbox(v_a_3374_);
lean_dec(v_a_3374_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3380_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v_c_3340_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_c_3340_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
else
{
lean_object* v___x_3382_; 
lean_del_object(v___x_3376_);
lean_inc_ref(v_c_3340_);
v___x_3382_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3340_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3391_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3391_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3391_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3340_, v_a_3383_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3387_);
v___x_3389_ = v___x_3385_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
else
{
lean_dec_ref(v_c_3340_);
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_c_3340_);
v_a_3393_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3373_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3373_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
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
else
{
goto v___jp_3352_;
}
}
else
{
goto v___jp_3352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec(v_a_3476_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3488_, lean_object* v_major_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3490_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; uint8_t v_trace_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v_trace_3499_ = lean_ctor_get_uint8(v_a_3498_, sizeof(void*)*18);
lean_dec(v_a_3498_);
if (v_trace_3499_ == 0)
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Meta_Grind_cases(v_mvarId_3488_, v_major_3489_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
return v___x_3500_;
}
else
{
lean_object* v___x_3501_; 
lean_inc(v_a_3495_);
lean_inc_ref(v_a_3494_);
lean_inc(v_a_3493_);
lean_inc_ref(v_a_3492_);
lean_inc_ref(v_major_3489_);
v___x_3501_ = lean_infer_type(v_major_3489_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = l_Lean_Meta_whnfD(v_a_3502_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = l_Lean_Expr_getAppFn(v_a_3504_);
lean_dec(v_a_3504_);
if (lean_obj_tag(v___x_3505_) == 4)
{
lean_object* v_declName_3506_; lean_object* v___x_3507_; 
v_declName_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_declName_3506_);
lean_dec_ref_known(v___x_3505_, 2);
v___x_3507_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3506_, v_a_3491_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3508_; 
lean_dec_ref_known(v___x_3507_, 1);
v___x_3508_ = l_Lean_Meta_Grind_cases(v_mvarId_3488_, v_major_3489_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
return v___x_3508_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v_major_3489_);
lean_dec(v_mvarId_3488_);
v_a_3509_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3507_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3507_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v___x_3517_; 
lean_dec_ref(v___x_3505_);
v___x_3517_ = l_Lean_Meta_Grind_cases(v_mvarId_3488_, v_major_3489_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
return v___x_3517_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v_major_3489_);
lean_dec(v_mvarId_3488_);
v_a_3518_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3503_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3503_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v_major_3489_);
lean_dec(v_mvarId_3488_);
v_a_3526_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3501_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3501_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref(v_major_3489_);
lean_dec(v_mvarId_3488_);
v_a_3534_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3497_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3497_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3542_, lean_object* v_major_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3542_, v_major_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3552_, lean_object* v_major_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3552_, v_major_3553_, v_a_3556_, v_a_3557_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3566_, lean_object* v_major_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3566_, v_major_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec(v_a_3568_);
return v_res_3579_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3580_){
_start:
{
uint64_t v_anchor_3581_; 
v_anchor_3581_ = lean_ctor_get_uint64(v_e_3580_, sizeof(void*)*3);
return v_anchor_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3582_){
_start:
{
uint64_t v_res_3583_; lean_object* v_r_3584_; 
v_res_3583_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3582_);
lean_dec_ref(v_e_3582_);
v_r_3584_ = lean_box_uint64(v_res_3583_);
return v_r_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3587_, lean_object* v_x_3588_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_box(0);
return v___x_3589_;
}
else
{
lean_object* v_key_3590_; lean_object* v_value_3591_; lean_object* v_tail_3592_; uint64_t v___x_3593_; uint8_t v___x_3594_; 
v_key_3590_ = lean_ctor_get(v_x_3588_, 0);
v_value_3591_ = lean_ctor_get(v_x_3588_, 1);
v_tail_3592_ = lean_ctor_get(v_x_3588_, 2);
v___x_3593_ = lean_unbox_uint64(v_key_3590_);
v___x_3594_ = lean_uint64_dec_eq(v___x_3593_, v_a_3587_);
if (v___x_3594_ == 0)
{
v_x_3588_ = v_tail_3592_;
goto _start;
}
else
{
lean_object* v___x_3596_; 
lean_inc(v_value_3591_);
v___x_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3596_, 0, v_value_3591_);
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3597_, lean_object* v_x_3598_){
_start:
{
uint64_t v_a_boxed_3599_; lean_object* v_res_3600_; 
v_a_boxed_3599_ = lean_unbox_uint64(v_a_3597_);
lean_dec_ref(v_a_3597_);
v_res_3600_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3599_, v_x_3598_);
lean_dec(v_x_3598_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3601_, uint64_t v_a_3602_){
_start:
{
lean_object* v_buckets_3603_; lean_object* v___x_3604_; uint64_t v___x_3605_; uint64_t v___x_3606_; uint64_t v_fold_3607_; uint64_t v___x_3608_; uint64_t v___x_3609_; uint64_t v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; size_t v___x_3613_; size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_buckets_3603_ = lean_ctor_get(v_m_3601_, 1);
v___x_3604_ = lean_array_get_size(v_buckets_3603_);
v___x_3605_ = 32ULL;
v___x_3606_ = lean_uint64_shift_right(v_a_3602_, v___x_3605_);
v_fold_3607_ = lean_uint64_xor(v_a_3602_, v___x_3606_);
v___x_3608_ = 16ULL;
v___x_3609_ = lean_uint64_shift_right(v_fold_3607_, v___x_3608_);
v___x_3610_ = lean_uint64_xor(v_fold_3607_, v___x_3609_);
v___x_3611_ = lean_uint64_to_usize(v___x_3610_);
v___x_3612_ = lean_usize_of_nat(v___x_3604_);
v___x_3613_ = ((size_t)1ULL);
v___x_3614_ = lean_usize_sub(v___x_3612_, v___x_3613_);
v___x_3615_ = lean_usize_land(v___x_3611_, v___x_3614_);
v___x_3616_ = lean_array_uget_borrowed(v_buckets_3603_, v___x_3615_);
v___x_3617_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3602_, v___x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3618_, lean_object* v_a_3619_){
_start:
{
uint64_t v_a_boxed_3620_; lean_object* v_res_3621_; 
v_a_boxed_3620_ = lean_unbox_uint64(v_a_3619_);
lean_dec_ref(v_a_3619_);
v_res_3621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3618_, v_a_boxed_3620_);
lean_dec_ref(v_m_3618_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
if (lean_obj_tag(v_x_3623_) == 0)
{
return v_x_3622_;
}
else
{
lean_object* v_key_3624_; lean_object* v_value_3625_; lean_object* v_tail_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3650_; 
v_key_3624_ = lean_ctor_get(v_x_3623_, 0);
v_value_3625_ = lean_ctor_get(v_x_3623_, 1);
v_tail_3626_ = lean_ctor_get(v_x_3623_, 2);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_x_3623_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3628_ = v_x_3623_;
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_tail_3626_);
lean_inc(v_value_3625_);
lean_inc(v_key_3624_);
lean_dec(v_x_3623_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v___x_3633_; uint64_t v___x_3634_; uint64_t v_fold_3635_; uint64_t v___x_3636_; uint64_t v___x_3637_; uint64_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; size_t v___x_3642_; size_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3630_ = lean_array_get_size(v_x_3622_);
v___x_3631_ = 32ULL;
v___x_3632_ = lean_unbox_uint64(v_key_3624_);
v___x_3633_ = lean_uint64_shift_right(v___x_3632_, v___x_3631_);
v___x_3634_ = lean_unbox_uint64(v_key_3624_);
v_fold_3635_ = lean_uint64_xor(v___x_3634_, v___x_3633_);
v___x_3636_ = 16ULL;
v___x_3637_ = lean_uint64_shift_right(v_fold_3635_, v___x_3636_);
v___x_3638_ = lean_uint64_xor(v_fold_3635_, v___x_3637_);
v___x_3639_ = lean_uint64_to_usize(v___x_3638_);
v___x_3640_ = lean_usize_of_nat(v___x_3630_);
v___x_3641_ = ((size_t)1ULL);
v___x_3642_ = lean_usize_sub(v___x_3640_, v___x_3641_);
v___x_3643_ = lean_usize_land(v___x_3639_, v___x_3642_);
v___x_3644_ = lean_array_uget_borrowed(v_x_3622_, v___x_3643_);
lean_inc(v___x_3644_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 2, v___x_3644_);
v___x_3646_ = v___x_3628_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_key_3624_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_value_3625_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_array_uset(v_x_3622_, v___x_3643_, v___x_3646_);
v_x_3622_ = v___x_3647_;
v_x_3623_ = v_tail_3626_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3651_, lean_object* v_source_3652_, lean_object* v_target_3653_){
_start:
{
lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3654_ = lean_array_get_size(v_source_3652_);
v___x_3655_ = lean_nat_dec_lt(v_i_3651_, v___x_3654_);
if (v___x_3655_ == 0)
{
lean_dec_ref(v_source_3652_);
lean_dec(v_i_3651_);
return v_target_3653_;
}
else
{
lean_object* v_es_3656_; lean_object* v___x_3657_; lean_object* v_source_3658_; lean_object* v_target_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_es_3656_ = lean_array_fget(v_source_3652_, v_i_3651_);
v___x_3657_ = lean_box(0);
v_source_3658_ = lean_array_fset(v_source_3652_, v_i_3651_, v___x_3657_);
v_target_3659_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3653_, v_es_3656_);
v___x_3660_ = lean_unsigned_to_nat(1u);
v___x_3661_ = lean_nat_add(v_i_3651_, v___x_3660_);
lean_dec(v_i_3651_);
v_i_3651_ = v___x_3661_;
v_source_3652_ = v_source_3658_;
v_target_3653_ = v_target_3659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3663_){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v_nbuckets_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3664_ = lean_array_get_size(v_data_3663_);
v___x_3665_ = lean_unsigned_to_nat(2u);
v_nbuckets_3666_ = lean_nat_mul(v___x_3664_, v___x_3665_);
v___x_3667_ = lean_unsigned_to_nat(0u);
v___x_3668_ = lean_box(0);
v___x_3669_ = lean_mk_array(v_nbuckets_3666_, v___x_3668_);
v___x_3670_ = lean_array_propagate_mark(v_data_3663_, v___x_3669_);
v___x_3671_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3667_, v_data_3663_, v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3672_, lean_object* v_b_3673_, lean_object* v_x_3674_){
_start:
{
if (lean_obj_tag(v_x_3674_) == 0)
{
lean_dec(v_b_3673_);
return v_x_3674_;
}
else
{
lean_object* v_key_3675_; lean_object* v_value_3676_; lean_object* v_tail_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3691_; 
v_key_3675_ = lean_ctor_get(v_x_3674_, 0);
v_value_3676_ = lean_ctor_get(v_x_3674_, 1);
v_tail_3677_ = lean_ctor_get(v_x_3674_, 2);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_x_3674_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3679_ = v_x_3674_;
v_isShared_3680_ = v_isSharedCheck_3691_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_tail_3677_);
lean_inc(v_value_3676_);
lean_inc(v_key_3675_);
lean_dec(v_x_3674_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3691_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
uint64_t v___x_3681_; uint8_t v___x_3682_; 
v___x_3681_ = lean_unbox_uint64(v_key_3675_);
v___x_3682_ = lean_uint64_dec_eq(v___x_3681_, v_a_3672_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3683_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3672_, v_b_3673_, v_tail_3677_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 2, v___x_3683_);
v___x_3685_ = v___x_3679_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_key_3675_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_value_3676_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_dec(v_value_3676_);
lean_dec(v_key_3675_);
v___x_3687_ = lean_box_uint64(v_a_3672_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 1, v_b_3673_);
lean_ctor_set(v___x_3679_, 0, v___x_3687_);
v___x_3689_ = v___x_3679_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_b_3673_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v_tail_3677_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3692_, lean_object* v_b_3693_, lean_object* v_x_3694_){
_start:
{
uint64_t v_a_boxed_3695_; lean_object* v_res_3696_; 
v_a_boxed_3695_ = lean_unbox_uint64(v_a_3692_);
lean_dec_ref(v_a_3692_);
v_res_3696_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3695_, v_b_3693_, v_x_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3697_, lean_object* v_x_3698_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 0)
{
uint8_t v___x_3699_; 
v___x_3699_ = 0;
return v___x_3699_;
}
else
{
lean_object* v_key_3700_; lean_object* v_tail_3701_; uint64_t v___x_3702_; uint8_t v___x_3703_; 
v_key_3700_ = lean_ctor_get(v_x_3698_, 0);
v_tail_3701_ = lean_ctor_get(v_x_3698_, 2);
v___x_3702_ = lean_unbox_uint64(v_key_3700_);
v___x_3703_ = lean_uint64_dec_eq(v___x_3702_, v_a_3697_);
if (v___x_3703_ == 0)
{
v_x_3698_ = v_tail_3701_;
goto _start;
}
else
{
return v___x_3703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3705_, lean_object* v_x_3706_){
_start:
{
uint64_t v_a_boxed_3707_; uint8_t v_res_3708_; lean_object* v_r_3709_; 
v_a_boxed_3707_ = lean_unbox_uint64(v_a_3705_);
lean_dec_ref(v_a_3705_);
v_res_3708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3707_, v_x_3706_);
lean_dec(v_x_3706_);
v_r_3709_ = lean_box(v_res_3708_);
return v_r_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3710_, uint64_t v_a_3711_, lean_object* v_b_3712_){
_start:
{
lean_object* v_size_3713_; lean_object* v_buckets_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3757_; 
v_size_3713_ = lean_ctor_get(v_m_3710_, 0);
v_buckets_3714_ = lean_ctor_get(v_m_3710_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_m_3710_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3716_ = v_m_3710_;
v_isShared_3717_ = v_isSharedCheck_3757_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_buckets_3714_);
lean_inc(v_size_3713_);
lean_dec(v_m_3710_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3757_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3718_; uint64_t v___x_3719_; uint64_t v___x_3720_; uint64_t v_fold_3721_; uint64_t v___x_3722_; uint64_t v___x_3723_; uint64_t v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; size_t v___x_3727_; size_t v___x_3728_; size_t v___x_3729_; lean_object* v_bkt_3730_; uint8_t v___x_3731_; 
v___x_3718_ = lean_array_get_size(v_buckets_3714_);
v___x_3719_ = 32ULL;
v___x_3720_ = lean_uint64_shift_right(v_a_3711_, v___x_3719_);
v_fold_3721_ = lean_uint64_xor(v_a_3711_, v___x_3720_);
v___x_3722_ = 16ULL;
v___x_3723_ = lean_uint64_shift_right(v_fold_3721_, v___x_3722_);
v___x_3724_ = lean_uint64_xor(v_fold_3721_, v___x_3723_);
v___x_3725_ = lean_uint64_to_usize(v___x_3724_);
v___x_3726_ = lean_usize_of_nat(v___x_3718_);
v___x_3727_ = ((size_t)1ULL);
v___x_3728_ = lean_usize_sub(v___x_3726_, v___x_3727_);
v___x_3729_ = lean_usize_land(v___x_3725_, v___x_3728_);
v_bkt_3730_ = lean_array_uget_borrowed(v_buckets_3714_, v___x_3729_);
v___x_3731_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3711_, v_bkt_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v_size_x27_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v_buckets_x27_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; uint8_t v___x_3742_; 
v___x_3732_ = lean_unsigned_to_nat(1u);
v_size_x27_3733_ = lean_nat_add(v_size_3713_, v___x_3732_);
lean_dec(v_size_3713_);
v___x_3734_ = lean_box_uint64(v_a_3711_);
lean_inc(v_bkt_3730_);
v___x_3735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
lean_ctor_set(v___x_3735_, 1, v_b_3712_);
lean_ctor_set(v___x_3735_, 2, v_bkt_3730_);
v_buckets_x27_3736_ = lean_array_uset(v_buckets_3714_, v___x_3729_, v___x_3735_);
v___x_3737_ = lean_unsigned_to_nat(4u);
v___x_3738_ = lean_nat_mul(v_size_x27_3733_, v___x_3737_);
v___x_3739_ = lean_unsigned_to_nat(3u);
v___x_3740_ = lean_nat_div(v___x_3738_, v___x_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_array_get_size(v_buckets_x27_3736_);
v___x_3742_ = lean_nat_dec_le(v___x_3740_, v___x_3741_);
lean_dec(v___x_3740_);
if (v___x_3742_ == 0)
{
lean_object* v_val_3743_; lean_object* v___x_3745_; 
v_val_3743_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3736_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 1, v_val_3743_);
lean_ctor_set(v___x_3716_, 0, v_size_x27_3733_);
v___x_3745_ = v___x_3716_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_size_x27_3733_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_val_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
else
{
lean_object* v___x_3748_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 1, v_buckets_x27_3736_);
lean_ctor_set(v___x_3716_, 0, v_size_x27_3733_);
v___x_3748_ = v___x_3716_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_size_x27_3733_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_buckets_x27_3736_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
else
{
lean_object* v___x_3750_; lean_object* v_buckets_x27_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
lean_inc(v_bkt_3730_);
v___x_3750_ = lean_box(0);
v_buckets_x27_3751_ = lean_array_uset(v_buckets_3714_, v___x_3729_, v___x_3750_);
v___x_3752_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3711_, v_b_3712_, v_bkt_3730_);
v___x_3753_ = lean_array_uset(v_buckets_x27_3751_, v___x_3729_, v___x_3752_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 1, v___x_3753_);
v___x_3755_ = v___x_3716_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_size_3713_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v___x_3753_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3758_, lean_object* v_a_3759_, lean_object* v_b_3760_){
_start:
{
uint64_t v_a_boxed_3761_; lean_object* v_res_3762_; 
v_a_boxed_3761_ = lean_unbox_uint64(v_a_3759_);
lean_dec_ref(v_a_3759_);
v_res_3762_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3758_, v_a_boxed_3761_, v_b_3760_);
return v_res_3762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_unsigned_to_nat(16u);
v___x_3765_ = lean_mk_array(v___x_3764_, v___x_3763_);
return v___x_3765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v_found_3768_; 
v___x_3766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3767_ = lean_unsigned_to_nat(0u);
v_found_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3768_, 0, v___x_3767_);
lean_ctor_set(v_found_3768_, 1, v___x_3766_);
return v_found_3768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_found_3769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3770_ = lean_box(0);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v_found_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3772_, lean_object* v_numDigits_3773_, lean_object* v_es_3774_, lean_object* v_as_3775_, size_t v_sz_3776_, size_t v_i_3777_, lean_object* v_b_3778_){
_start:
{
lean_object* v_a_3780_; uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3777_, v_sz_3776_);
if (v___x_3784_ == 0)
{
return v_b_3778_;
}
else
{
lean_object* v_snd_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3819_; 
v_snd_3785_ = lean_ctor_get(v_b_3778_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_b_3778_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; 
v_unused_3820_ = lean_ctor_get(v_b_3778_, 0);
lean_dec(v_unused_3820_);
v___x_3787_ = v_b_3778_;
v_isShared_3788_ = v_isSharedCheck_3819_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_snd_3785_);
lean_dec(v_b_3778_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3819_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v_a_3789_; uint64_t v_anchor_3790_; lean_object* v___x_3791_; uint64_t v___x_3792_; uint64_t v___x_3793_; lean_object* v___x_3794_; 
v_a_3789_ = lean_array_uget_borrowed(v_as_3775_, v_i_3777_);
v_anchor_3790_ = lean_ctor_get_uint64(v_a_3789_, sizeof(void*)*3);
v___x_3791_ = lean_box(0);
v___x_3792_ = lean_uint64_of_nat(v_shift_3772_);
v___x_3793_ = lean_uint64_shift_right(v_anchor_3790_, v___x_3792_);
v___x_3794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3785_, v___x_3793_);
if (lean_obj_tag(v___x_3794_) == 1)
{
lean_object* v_val_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3813_; 
v_val_3795_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3797_ = v___x_3794_;
v_isShared_3798_ = v_isSharedCheck_3813_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_val_3795_);
lean_dec(v___x_3794_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3813_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
uint64_t v___x_3799_; uint8_t v___x_3800_; 
v___x_3799_ = lean_unbox_uint64(v_val_3795_);
lean_dec(v_val_3795_);
v___x_3800_ = lean_uint64_dec_eq(v___x_3799_, v_anchor_3790_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3801_ = lean_unsigned_to_nat(1u);
v___x_3802_ = lean_nat_add(v_numDigits_3773_, v___x_3801_);
v___x_3803_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3774_, v___x_3802_);
lean_dec(v___x_3802_);
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 0, v___x_3803_);
v___x_3805_ = v___x_3797_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3805_);
v___x_3807_ = v___x_3787_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_snd_3785_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
else
{
lean_object* v___x_3811_; 
lean_del_object(v___x_3797_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3791_);
v___x_3811_ = v___x_3787_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_snd_3785_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v_a_3780_ = v___x_3811_;
goto v___jp_3779_;
}
}
}
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec(v___x_3794_);
v___x_3814_ = lean_box_uint64(v_anchor_3790_);
v___x_3815_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3785_, v___x_3793_, v___x_3814_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v___x_3815_);
lean_ctor_set(v___x_3787_, 0, v___x_3791_);
v___x_3817_ = v___x_3787_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
v_a_3780_ = v___x_3817_;
goto v___jp_3779_;
}
}
}
}
v___jp_3779_:
{
size_t v___x_3781_; size_t v___x_3782_; 
v___x_3781_ = ((size_t)1ULL);
v___x_3782_ = lean_usize_add(v_i_3777_, v___x_3781_);
v_i_3777_ = v___x_3782_;
v_b_3778_ = v_a_3780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3821_, lean_object* v_numDigits_3822_){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3823_ = lean_unsigned_to_nat(4u);
v___x_3824_ = lean_nat_mul(v___x_3823_, v_numDigits_3822_);
v___x_3825_ = lean_unsigned_to_nat(64u);
v___x_3826_ = lean_nat_dec_lt(v___x_3824_, v___x_3825_);
if (v___x_3826_ == 0)
{
lean_dec(v___x_3824_);
lean_inc(v_numDigits_3822_);
return v_numDigits_3822_;
}
else
{
lean_object* v_shift_3827_; lean_object* v___x_3828_; size_t v_sz_3829_; size_t v___x_3830_; lean_object* v___x_3831_; lean_object* v_fst_3832_; 
v_shift_3827_ = lean_nat_sub(v___x_3825_, v___x_3824_);
lean_dec(v___x_3824_);
v___x_3828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3829_ = lean_array_size(v_es_3821_);
v___x_3830_ = ((size_t)0ULL);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3827_, v_numDigits_3822_, v_es_3821_, v_es_3821_, v_sz_3829_, v___x_3830_, v___x_3828_);
lean_dec(v_shift_3827_);
v_fst_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_fst_3832_);
lean_dec_ref(v___x_3831_);
if (lean_obj_tag(v_fst_3832_) == 0)
{
lean_inc(v_numDigits_3822_);
return v_numDigits_3822_;
}
else
{
lean_object* v_val_3833_; 
v_val_3833_ = lean_ctor_get(v_fst_3832_, 0);
lean_inc(v_val_3833_);
lean_dec_ref_known(v_fst_3832_, 1);
return v_val_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3834_, lean_object* v_numDigits_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3834_, v_numDigits_3835_);
lean_dec(v_numDigits_3835_);
lean_dec_ref(v_es_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3837_, lean_object* v_numDigits_3838_, lean_object* v_es_3839_, lean_object* v_as_3840_, lean_object* v_sz_3841_, lean_object* v_i_3842_, lean_object* v_b_3843_){
_start:
{
size_t v_sz_boxed_3844_; size_t v_i_boxed_3845_; lean_object* v_res_3846_; 
v_sz_boxed_3844_ = lean_unbox_usize(v_sz_3841_);
lean_dec(v_sz_3841_);
v_i_boxed_3845_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_res_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3837_, v_numDigits_3838_, v_es_3839_, v_as_3840_, v_sz_boxed_3844_, v_i_boxed_3845_, v_b_3843_);
lean_dec_ref(v_as_3840_);
lean_dec_ref(v_es_3839_);
lean_dec(v_numDigits_3838_);
lean_dec(v_shift_3837_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3847_){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_unsigned_to_nat(4u);
v___x_3849_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3847_, v___x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3850_);
lean_dec_ref(v_es_3850_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3852_, lean_object* v_as_3853_, size_t v_i_3854_, size_t v_stop_3855_, lean_object* v_b_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_a_3869_; uint8_t v___x_3873_; 
v___x_3873_ = lean_usize_dec_eq(v_i_3854_, v_stop_3855_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v_e_3875_; lean_object* v___x_3876_; 
v___x_3874_ = lean_array_uget_borrowed(v_as_3853_, v_i_3854_);
v_e_3875_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3874_);
v___x_3876_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3874_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
lean_inc(v___x_3874_);
v___x_3878_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3874_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
if (lean_obj_tag(v_a_3879_) == 2)
{
lean_object* v_numCases_3880_; uint8_t v_isRec_3881_; lean_object* v___x_3882_; 
v_numCases_3880_ = lean_ctor_get(v_a_3879_, 0);
lean_inc(v_numCases_3880_);
v_isRec_3881_ = lean_ctor_get_uint8(v_a_3879_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3879_, 1);
lean_inc_ref(v_filter_3852_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc(v___y_3864_);
lean_inc_ref(v___y_3863_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v_e_3875_);
v___x_3882_ = lean_apply_12(v_filter_3852_, v_e_3875_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, lean_box(0));
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; uint8_t v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v___x_3884_ = lean_unbox(v_a_3883_);
lean_dec(v_a_3883_);
if (v___x_3884_ == 0)
{
lean_dec(v_numCases_3880_);
lean_dec(v_a_3877_);
lean_dec_ref(v_e_3875_);
v_a_3869_ = v_b_3856_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3885_; uint64_t v___x_3886_; lean_object* v___x_3887_; 
lean_inc(v___x_3874_);
v___x_3885_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3885_, 0, v___x_3874_);
lean_ctor_set(v___x_3885_, 1, v_numCases_3880_);
lean_ctor_set(v___x_3885_, 2, v_e_3875_);
lean_ctor_set_uint8(v___x_3885_, sizeof(void*)*3 + 8, v_isRec_3881_);
v___x_3886_ = lean_unbox_uint64(v_a_3877_);
lean_dec(v_a_3877_);
lean_ctor_set_uint64(v___x_3885_, sizeof(void*)*3, v___x_3886_);
v___x_3887_ = lean_array_push(v_b_3856_, v___x_3885_);
v_a_3869_ = v___x_3887_;
goto v___jp_3868_;
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_numCases_3880_);
lean_dec(v_a_3877_);
lean_dec_ref(v_e_3875_);
lean_dec_ref(v_b_3856_);
lean_dec_ref(v_filter_3852_);
v_a_3888_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3882_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3882_);
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
else
{
lean_dec(v_a_3879_);
lean_dec(v_a_3877_);
lean_dec_ref(v_e_3875_);
v_a_3869_ = v_b_3856_;
goto v___jp_3868_;
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec(v_a_3877_);
lean_dec_ref(v_e_3875_);
lean_dec_ref(v_b_3856_);
lean_dec_ref(v_filter_3852_);
v_a_3896_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3878_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3878_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec_ref(v_e_3875_);
lean_dec_ref(v_b_3856_);
lean_dec_ref(v_filter_3852_);
v_a_3904_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3876_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3876_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
lean_object* v___x_3912_; 
lean_dec_ref(v_filter_3852_);
v___x_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3912_, 0, v_b_3856_);
return v___x_3912_;
}
v___jp_3868_:
{
size_t v___x_3870_; size_t v___x_3871_; 
v___x_3870_ = ((size_t)1ULL);
v___x_3871_ = lean_usize_add(v_i_3854_, v___x_3870_);
v_i_3854_ = v___x_3871_;
v_b_3856_ = v_a_3869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3913_, lean_object* v_as_3914_, lean_object* v_i_3915_, lean_object* v_stop_3916_, lean_object* v_b_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
size_t v_i_boxed_3929_; size_t v_stop_boxed_3930_; lean_object* v_res_3931_; 
v_i_boxed_3929_ = lean_unbox_usize(v_i_3915_);
lean_dec(v_i_3915_);
v_stop_boxed_3930_ = lean_unbox_usize(v_stop_3916_);
lean_dec(v_stop_3916_);
v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3913_, v_as_3914_, v_i_boxed_3929_, v_stop_boxed_3930_, v_b_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v_as_3914_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3934_, lean_object* v_as_3935_, lean_object* v_start_3936_, lean_object* v_stop_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3949_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3950_ = lean_nat_dec_lt(v_start_3936_, v_stop_3937_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec_ref(v_filter_3934_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = lean_array_get_size(v_as_3935_);
v___x_3953_ = lean_nat_dec_le(v_stop_3937_, v___x_3952_);
if (v___x_3953_ == 0)
{
uint8_t v___x_3954_; 
v___x_3954_ = lean_nat_dec_lt(v_start_3936_, v___x_3952_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; 
lean_dec_ref(v_filter_3934_);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3949_);
return v___x_3955_;
}
else
{
size_t v___x_3956_; size_t v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_usize_of_nat(v_start_3936_);
v___x_3957_ = lean_usize_of_nat(v___x_3952_);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3934_, v_as_3935_, v___x_3956_, v___x_3957_, v___x_3949_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
return v___x_3958_;
}
}
else
{
size_t v___x_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = lean_usize_of_nat(v_start_3936_);
v___x_3960_ = lean_usize_of_nat(v_stop_3937_);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3934_, v_as_3935_, v___x_3959_, v___x_3960_, v___x_3949_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3962_, lean_object* v_as_3963_, lean_object* v_start_3964_, lean_object* v_stop_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3962_, v_as_3963_, v_start_3964_, v_stop_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v_stop_3965_);
lean_dec(v_start_3964_);
lean_dec_ref(v_as_3963_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3978_, lean_object* v_candidates_x3f_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_candidates_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; 
if (lean_obj_tag(v_candidates_x3f_3979_) == 0)
{
lean_object* v___x_4025_; lean_object* v_toGoalState_4026_; lean_object* v_split_4027_; lean_object* v_candidates_4028_; 
v___x_4025_ = lean_st_ref_get(v_a_3980_);
v_toGoalState_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc_ref(v_toGoalState_4026_);
lean_dec(v___x_4025_);
v_split_4027_ = lean_ctor_get(v_toGoalState_4026_, 15);
lean_inc_ref(v_split_4027_);
lean_dec_ref(v_toGoalState_4026_);
v_candidates_4028_ = lean_ctor_get(v_split_4027_, 0);
lean_inc(v_candidates_4028_);
lean_dec_ref(v_split_4027_);
v_candidates_3992_ = v_candidates_4028_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
v___y_4002_ = v_a_3989_;
goto v___jp_3991_;
}
else
{
lean_object* v_val_4029_; 
v_val_4029_ = lean_ctor_get(v_candidates_x3f_3979_, 0);
lean_inc(v_val_4029_);
lean_dec_ref_known(v_candidates_x3f_3979_, 1);
v_candidates_3992_ = v_val_4029_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
v___y_4002_ = v_a_3989_;
goto v___jp_3991_;
}
v___jp_3991_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4003_ = lean_array_mk(v_candidates_3992_);
v___x_4004_ = lean_unsigned_to_nat(0u);
v___x_4005_ = lean_array_get_size(v___x_4003_);
v___x_4006_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3978_, v___x_4003_, v___x_4004_, v___x_4005_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec_ref(v___x_4003_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4016_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4009_ = v___x_4006_;
v_isShared_4010_ = v_isSharedCheck_4016_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_4006_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4016_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4011_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4007_);
v___x_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4012_, 0, v_a_4007_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v___x_4012_);
v___x_4014_ = v___x_4009_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
v_a_4017_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4006_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4006_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4030_, lean_object* v_candidates_x3f_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4030_, v_candidates_x3f_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec(v_a_4032_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4044_, lean_object* v_m_4045_, uint64_t v_a_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4045_, v_a_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4048_, lean_object* v_m_4049_, lean_object* v_a_4050_){
_start:
{
uint64_t v_a_boxed_4051_; lean_object* v_res_4052_; 
v_a_boxed_4051_ = lean_unbox_uint64(v_a_4050_);
lean_dec_ref(v_a_4050_);
v_res_4052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4048_, v_m_4049_, v_a_boxed_4051_);
lean_dec_ref(v_m_4049_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4053_, lean_object* v_m_4054_, uint64_t v_a_4055_, lean_object* v_b_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4054_, v_a_4055_, v_b_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4058_, lean_object* v_m_4059_, lean_object* v_a_4060_, lean_object* v_b_4061_){
_start:
{
uint64_t v_a_boxed_4062_; lean_object* v_res_4063_; 
v_a_boxed_4062_ = lean_unbox_uint64(v_a_4060_);
lean_dec_ref(v_a_4060_);
v_res_4063_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4058_, v_m_4059_, v_a_boxed_4062_, v_b_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4064_, uint64_t v_a_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4068_, lean_object* v_a_4069_, lean_object* v_x_4070_){
_start:
{
uint64_t v_a_boxed_4071_; lean_object* v_res_4072_; 
v_a_boxed_4071_ = lean_unbox_uint64(v_a_4069_);
lean_dec_ref(v_a_4069_);
v_res_4072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4068_, v_a_boxed_4071_, v_x_4070_);
lean_dec(v_x_4070_);
return v_res_4072_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4073_, uint64_t v_a_4074_, lean_object* v_x_4075_){
_start:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4074_, v_x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4077_, lean_object* v_a_4078_, lean_object* v_x_4079_){
_start:
{
uint64_t v_a_boxed_4080_; uint8_t v_res_4081_; lean_object* v_r_4082_; 
v_a_boxed_4080_ = lean_unbox_uint64(v_a_4078_);
lean_dec_ref(v_a_4078_);
v_res_4081_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4077_, v_a_boxed_4080_, v_x_4079_);
lean_dec(v_x_4079_);
v_r_4082_ = lean_box(v_res_4081_);
return v_r_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4083_, lean_object* v_data_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4086_, uint64_t v_a_4087_, lean_object* v_b_4088_, lean_object* v_x_4089_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4087_, v_b_4088_, v_x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4091_, lean_object* v_a_4092_, lean_object* v_b_4093_, lean_object* v_x_4094_){
_start:
{
uint64_t v_a_boxed_4095_; lean_object* v_res_4096_; 
v_a_boxed_4095_ = lean_unbox_uint64(v_a_4092_);
lean_dec_ref(v_a_4092_);
v_res_4096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4091_, v_a_boxed_4095_, v_b_4093_, v_x_4094_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4097_, lean_object* v_i_4098_, lean_object* v_source_4099_, lean_object* v_target_4100_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4098_, v_source_4099_, v_target_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4102_, lean_object* v_x_4103_, lean_object* v_x_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4103_, v_x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4118_ = 1;
v___x_4119_ = lean_box(v___x_4118_);
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v_x_4121_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4134_, uint64_t v_a_4135_, lean_object* v_c_4136_, lean_object* v_numDigits_4137_, lean_object* v_as_4138_, size_t v_sz_4139_, size_t v_i_4140_, lean_object* v_b_4141_){
_start:
{
lean_object* v_a_4144_; uint8_t v___x_4148_; 
v___x_4148_ = lean_usize_dec_lt(v_i_4140_, v_sz_4139_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; 
lean_dec(v_numDigits_4137_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_b_4141_);
return v___x_4149_;
}
else
{
lean_object* v_snd_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4176_; 
v_snd_4150_ = lean_ctor_get(v_b_4141_, 1);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_b_4141_);
if (v_isSharedCheck_4176_ == 0)
{
lean_object* v_unused_4177_; 
v_unused_4177_ = lean_ctor_get(v_b_4141_, 0);
lean_dec(v_unused_4177_);
v___x_4152_ = v_b_4141_;
v_isShared_4153_ = v_isSharedCheck_4176_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_snd_4150_);
lean_dec(v_b_4141_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4176_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v_a_4154_; lean_object* v_c_4155_; uint64_t v_anchor_4156_; lean_object* v___x_4157_; uint64_t v___x_4158_; uint64_t v___x_4159_; uint8_t v___x_4160_; 
v_a_4154_ = lean_array_uget_borrowed(v_as_4138_, v_i_4140_);
v_c_4155_ = lean_ctor_get(v_a_4154_, 0);
v_anchor_4156_ = lean_ctor_get_uint64(v_a_4154_, sizeof(void*)*3);
v___x_4157_ = lean_box(0);
v___x_4158_ = lean_uint64_shift_right(v_anchor_4156_, v___x_4134_);
v___x_4159_ = lean_uint64_shift_right(v_a_4135_, v___x_4134_);
v___x_4160_ = lean_uint64_dec_eq(v___x_4158_, v___x_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4162_; 
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4157_);
v___x_4162_ = v___x_4152_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_snd_4150_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
v_a_4144_ = v___x_4162_;
goto v___jp_4143_;
}
}
else
{
uint8_t v___x_4164_; 
v___x_4164_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4155_, v_c_4136_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4168_; 
v___x_4165_ = lean_unsigned_to_nat(1u);
v___x_4166_ = lean_nat_add(v_snd_4150_, v___x_4165_);
lean_dec(v_snd_4150_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v___x_4166_);
lean_ctor_set(v___x_4152_, 0, v___x_4157_);
v___x_4168_ = v___x_4152_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v___x_4166_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
v_a_4144_ = v___x_4168_;
goto v___jp_4143_;
}
}
else
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
lean_inc(v_snd_4150_);
v___x_4170_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4170_, 0, v_numDigits_4137_);
lean_ctor_set(v___x_4170_, 1, v_snd_4150_);
lean_ctor_set_uint64(v___x_4170_, sizeof(void*)*2, v_a_4135_);
v___x_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4171_);
v___x_4173_ = v___x_4152_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4171_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v_snd_4150_);
v___x_4173_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; 
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
}
}
}
v___jp_4143_:
{
size_t v___x_4145_; size_t v___x_4146_; 
v___x_4145_ = ((size_t)1ULL);
v___x_4146_ = lean_usize_add(v_i_4140_, v___x_4145_);
v_i_4140_ = v___x_4146_;
v_b_4141_ = v_a_4144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4178_, lean_object* v_a_4179_, lean_object* v_c_4180_, lean_object* v_numDigits_4181_, lean_object* v_as_4182_, lean_object* v_sz_4183_, lean_object* v_i_4184_, lean_object* v_b_4185_, lean_object* v___y_4186_){
_start:
{
uint64_t v___x_7695__boxed_4187_; uint64_t v_a_7696__boxed_4188_; size_t v_sz_boxed_4189_; size_t v_i_boxed_4190_; lean_object* v_res_4191_; 
v___x_7695__boxed_4187_ = lean_unbox_uint64(v___x_4178_);
lean_dec_ref(v___x_4178_);
v_a_7696__boxed_4188_ = lean_unbox_uint64(v_a_4179_);
lean_dec_ref(v_a_4179_);
v_sz_boxed_4189_ = lean_unbox_usize(v_sz_4183_);
lean_dec(v_sz_4183_);
v_i_boxed_4190_ = lean_unbox_usize(v_i_4184_);
lean_dec(v_i_4184_);
v_res_4191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7695__boxed_4187_, v_a_7696__boxed_4188_, v_c_4180_, v_numDigits_4181_, v_as_4182_, v_sz_boxed_4189_, v_i_boxed_4190_, v_b_4185_);
lean_dec_ref(v_as_4182_);
lean_dec_ref(v_c_4180_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4196_, lean_object* v_candidates_x3f_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v___f_4209_; lean_object* v___x_4210_; 
v___f_4209_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4210_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4209_, v_candidates_x3f_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v_candidates_4212_; lean_object* v_numDigits_4213_; lean_object* v___x_4214_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
v_candidates_4212_ = lean_ctor_get(v_a_4211_, 0);
lean_inc_ref(v_candidates_4212_);
v_numDigits_4213_ = lean_ctor_get(v_a_4211_, 1);
lean_inc(v_numDigits_4213_);
lean_dec(v_a_4211_);
v___x_4214_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4196_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint64_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; size_t v_sz_4223_; size_t v___x_4224_; uint64_t v___x_4225_; lean_object* v___x_4226_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4216_ = lean_unsigned_to_nat(64u);
v___x_4217_ = lean_unsigned_to_nat(4u);
v___x_4218_ = lean_nat_mul(v___x_4217_, v_numDigits_4213_);
v___x_4219_ = lean_nat_sub(v___x_4216_, v___x_4218_);
lean_dec(v___x_4218_);
v___x_4220_ = lean_uint64_of_nat(v___x_4219_);
lean_dec(v___x_4219_);
v___x_4221_ = lean_unsigned_to_nat(0u);
v___x_4222_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4223_ = lean_array_size(v_candidates_4212_);
v___x_4224_ = ((size_t)0ULL);
v___x_4225_ = lean_unbox_uint64(v_a_4215_);
lean_inc(v_numDigits_4213_);
v___x_4226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4220_, v___x_4225_, v_c_4196_, v_numDigits_4213_, v_candidates_4212_, v_sz_4223_, v___x_4224_, v___x_4222_);
lean_dec_ref(v_candidates_4212_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4241_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4241_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4241_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v_fst_4231_; 
v_fst_4231_ = lean_ctor_get(v_a_4227_, 0);
lean_inc(v_fst_4231_);
lean_dec(v_a_4227_);
if (lean_obj_tag(v_fst_4231_) == 0)
{
lean_object* v___x_4232_; uint64_t v___x_4233_; lean_object* v___x_4235_; 
v___x_4232_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4232_, 0, v_numDigits_4213_);
lean_ctor_set(v___x_4232_, 1, v___x_4221_);
v___x_4233_ = lean_unbox_uint64(v_a_4215_);
lean_dec(v_a_4215_);
lean_ctor_set_uint64(v___x_4232_, sizeof(void*)*2, v___x_4233_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4232_);
v___x_4235_ = v___x_4229_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4232_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
else
{
lean_object* v_val_4237_; lean_object* v___x_4239_; 
lean_dec(v_a_4215_);
lean_dec(v_numDigits_4213_);
v_val_4237_ = lean_ctor_get(v_fst_4231_, 0);
lean_inc(v_val_4237_);
lean_dec_ref_known(v_fst_4231_, 1);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v_val_4237_);
v___x_4239_ = v___x_4229_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_val_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec(v_a_4215_);
lean_dec(v_numDigits_4213_);
v_a_4242_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4226_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4226_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec(v_numDigits_4213_);
lean_dec_ref(v_candidates_4212_);
v_a_4250_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4214_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4214_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_a_4258_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4210_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4210_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4266_, lean_object* v_candidates_x3f_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4266_, v_candidates_x3f_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_c_4266_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4280_, uint64_t v_a_4281_, lean_object* v_c_4282_, lean_object* v_numDigits_4283_, lean_object* v_as_4284_, size_t v_sz_4285_, size_t v_i_4286_, lean_object* v_b_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4280_, v_a_4281_, v_c_4282_, v_numDigits_4283_, v_as_4284_, v_sz_4285_, v_i_4286_, v_b_4287_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4300_ = _args[0];
lean_object* v_a_4301_ = _args[1];
lean_object* v_c_4302_ = _args[2];
lean_object* v_numDigits_4303_ = _args[3];
lean_object* v_as_4304_ = _args[4];
lean_object* v_sz_4305_ = _args[5];
lean_object* v_i_4306_ = _args[6];
lean_object* v_b_4307_ = _args[7];
lean_object* v___y_4308_ = _args[8];
lean_object* v___y_4309_ = _args[9];
lean_object* v___y_4310_ = _args[10];
lean_object* v___y_4311_ = _args[11];
lean_object* v___y_4312_ = _args[12];
lean_object* v___y_4313_ = _args[13];
lean_object* v___y_4314_ = _args[14];
lean_object* v___y_4315_ = _args[15];
lean_object* v___y_4316_ = _args[16];
lean_object* v___y_4317_ = _args[17];
lean_object* v___y_4318_ = _args[18];
_start:
{
uint64_t v___x_7894__boxed_4319_; uint64_t v_a_7895__boxed_4320_; size_t v_sz_boxed_4321_; size_t v_i_boxed_4322_; lean_object* v_res_4323_; 
v___x_7894__boxed_4319_ = lean_unbox_uint64(v___x_4300_);
lean_dec_ref(v___x_4300_);
v_a_7895__boxed_4320_ = lean_unbox_uint64(v_a_4301_);
lean_dec_ref(v_a_4301_);
v_sz_boxed_4321_ = lean_unbox_usize(v_sz_4305_);
lean_dec(v_sz_4305_);
v_i_boxed_4322_ = lean_unbox_usize(v_i_4306_);
lean_dec(v_i_4306_);
v_res_4323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7894__boxed_4319_, v_a_7895__boxed_4320_, v_c_4302_, v_numDigits_4303_, v_as_4304_, v_sz_boxed_4321_, v_i_boxed_4322_, v_b_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v_as_4304_);
lean_dec_ref(v_c_4302_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_numDigits_4351_; uint64_t v_anchor_4352_; lean_object* v_ordinal_4353_; lean_object* v___x_4354_; 
v_numDigits_4351_ = lean_ctor_get(v_info_4348_, 0);
v_anchor_4352_ = lean_ctor_get_uint64(v_info_4348_, sizeof(void*)*2);
v_ordinal_4353_ = lean_ctor_get(v_info_4348_, 1);
v___x_4354_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4351_, v_anchor_4352_, v_a_4349_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4391_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4391_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4391_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4359_ = lean_unsigned_to_nat(0u);
v___x_4360_ = lean_nat_dec_eq(v_ordinal_4353_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_object* v_ref_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
v_ref_4361_ = lean_ctor_get(v_a_4349_, 2);
v___x_4362_ = l_Lean_SourceInfo_fromRef(v_ref_4361_, v___x_4360_);
v___x_4363_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4364_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4362_, 3);
v___x_4365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4362_);
lean_ctor_set(v___x_4365_, 1, v___x_4363_);
v___x_4366_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4367_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4362_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = lean_unsigned_to_nat(1u);
v___x_4370_ = lean_nat_add(v_ordinal_4353_, v___x_4369_);
v___x_4371_ = l_Nat_reprFast(v___x_4370_);
v___x_4372_ = lean_box(2);
v___x_4373_ = l_Lean_Syntax_mkNumLit(v___x_4371_, v___x_4372_);
v___x_4374_ = l_Lean_Syntax_node3(v___x_4362_, v___x_4366_, v_a_4355_, v___x_4368_, v___x_4373_);
v___x_4375_ = l_Lean_Syntax_node2(v___x_4362_, v___x_4364_, v___x_4365_, v___x_4374_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4375_);
v___x_4377_ = v___x_4357_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
else
{
lean_object* v_ref_4379_; uint8_t v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
v_ref_4379_ = lean_ctor_get(v_a_4349_, 2);
v___x_4380_ = 0;
v___x_4381_ = l_Lean_SourceInfo_fromRef(v_ref_4379_, v___x_4380_);
v___x_4382_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4383_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4381_, 2);
v___x_4384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4381_);
lean_ctor_set(v___x_4384_, 1, v___x_4382_);
v___x_4385_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4386_ = l_Lean_Syntax_node1(v___x_4381_, v___x_4385_, v_a_4355_);
v___x_4387_ = l_Lean_Syntax_node2(v___x_4381_, v___x_4383_, v___x_4384_, v___x_4386_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4387_);
v___x_4389_ = v___x_4357_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
else
{
return v___x_4354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4392_, v_a_4393_);
lean_dec_ref(v_a_4393_);
lean_dec_ref(v_info_4392_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4396_, v_a_4397_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4401_, v_a_4402_, v_a_4403_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec_ref(v_info_4401_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(lean_object* v_proof_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v_p_4437_; lean_object* v___x_4440_; 
lean_inc_ref(v_proof_4418_);
v___x_4440_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4418_, v_a_4420_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4467_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4443_ = v___x_4440_;
v_isShared_4444_ = v_isSharedCheck_4467_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4440_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4467_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4445_; uint8_t v___x_4446_; 
v___x_4445_ = l_Lean_Expr_cleanupAnnotations(v_a_4441_);
lean_dec(v_a_4441_);
v___x_4446_ = l_Lean_Expr_isApp(v___x_4445_);
if (v___x_4446_ == 0)
{
lean_dec_ref(v___x_4445_);
lean_del_object(v___x_4443_);
v___y_4425_ = v_a_4419_;
v___y_4426_ = v_a_4420_;
v___y_4427_ = v_a_4421_;
v___y_4428_ = v_a_4422_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4445_);
v___x_4448_ = l_Lean_Expr_isApp(v___x_4447_);
if (v___x_4448_ == 0)
{
lean_dec_ref(v___x_4447_);
lean_dec_ref(v___x_4445_);
lean_del_object(v___x_4443_);
v___y_4425_ = v_a_4419_;
v___y_4426_ = v_a_4420_;
v___y_4427_ = v_a_4421_;
v___y_4428_ = v_a_4422_;
goto v___jp_4424_;
}
else
{
lean_object* v_arg_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; uint8_t v___x_4452_; 
v_arg_4449_ = lean_ctor_get(v___x_4445_, 1);
lean_inc_ref(v_arg_4449_);
lean_dec_ref(v___x_4445_);
v___x_4450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4447_);
v___x_4451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4452_ = l_Lean_Expr_isConstOf(v___x_4450_, v___x_4451_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; uint8_t v___x_4454_; 
lean_dec_ref(v___x_4447_);
lean_del_object(v___x_4443_);
v___x_4453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4454_ = l_Lean_Expr_isConstOf(v___x_4450_, v___x_4453_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4456_ = l_Lean_Expr_isConstOf(v___x_4450_, v___x_4455_);
lean_dec_ref(v___x_4450_);
if (v___x_4456_ == 0)
{
lean_dec_ref(v_arg_4449_);
v___y_4425_ = v_a_4419_;
v___y_4426_ = v_a_4420_;
v___y_4427_ = v_a_4421_;
v___y_4428_ = v_a_4422_;
goto v___jp_4424_;
}
else
{
lean_dec_ref(v_proof_4418_);
v_p_4437_ = v_arg_4449_;
goto v___jp_4436_;
}
}
else
{
lean_dec_ref(v___x_4450_);
lean_dec_ref(v_proof_4418_);
v_p_4437_ = v_arg_4449_;
goto v___jp_4436_;
}
}
else
{
lean_object* v_arg_4457_; uint8_t v___x_4458_; 
lean_dec_ref(v___x_4450_);
lean_dec_ref(v_proof_4418_);
v_arg_4457_ = lean_ctor_get(v___x_4447_, 1);
lean_inc_ref(v_arg_4457_);
lean_dec_ref(v___x_4447_);
v___x_4458_ = l_Lean_Expr_isFalse(v_arg_4457_);
lean_dec_ref(v_arg_4457_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4459_; lean_object* v___x_4461_; 
lean_dec_ref(v_arg_4449_);
v___x_4459_ = lean_box(0);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4459_);
v___x_4461_ = v___x_4443_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_arg_4449_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4463_);
v___x_4465_ = v___x_4443_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v_proof_4418_);
v_a_4468_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4440_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4440_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
v___jp_4424_:
{
if (lean_obj_tag(v_proof_4418_) == 6)
{
lean_object* v_body_4429_; uint8_t v___x_4430_; 
v_body_4429_ = lean_ctor_get(v_proof_4418_, 2);
lean_inc_ref(v_body_4429_);
lean_dec_ref_known(v_proof_4418_, 3);
v___x_4430_ = l_Lean_Expr_hasLooseBVars(v_body_4429_);
if (v___x_4430_ == 0)
{
v_proof_4418_ = v_body_4429_;
v_a_4419_ = v___y_4425_;
v_a_4420_ = v___y_4426_;
v_a_4421_ = v___y_4427_;
v_a_4422_ = v___y_4428_;
goto _start;
}
else
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
lean_dec_ref(v_body_4429_);
v___x_4432_ = lean_box(0);
v___x_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
return v___x_4433_;
}
}
else
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
lean_dec_ref(v_proof_4418_);
v___x_4434_ = lean_box(0);
v___x_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
v___jp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4438_, 0, v_p_4437_);
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
return v___x_4439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___boxed(lean_object* v_proof_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_proof_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
lean_dec(v_a_4480_);
lean_dec_ref(v_a_4479_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(lean_object* v_e_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v___x_4486_; 
v___x_4486_ = l_Lean_Expr_hasMVar(v_e_4483_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
v___x_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4487_, 0, v_e_4483_);
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; lean_object* v_mctx_4489_; lean_object* v___x_4490_; lean_object* v_fst_4491_; lean_object* v_snd_4492_; lean_object* v___x_4493_; lean_object* v_cache_4494_; lean_object* v_zetaDeltaFVarIds_4495_; lean_object* v_postponed_4496_; lean_object* v_diag_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4506_; 
v___x_4488_ = lean_st_ref_get(v___y_4484_);
v_mctx_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc_ref(v_mctx_4489_);
lean_dec(v___x_4488_);
v___x_4490_ = l_Lean_instantiateMVarsCore(v_mctx_4489_, v_e_4483_);
v_fst_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_fst_4491_);
v_snd_4492_ = lean_ctor_get(v___x_4490_, 1);
lean_inc(v_snd_4492_);
lean_dec_ref(v___x_4490_);
v___x_4493_ = lean_st_ref_take(v___y_4484_);
v_cache_4494_ = lean_ctor_get(v___x_4493_, 1);
v_zetaDeltaFVarIds_4495_ = lean_ctor_get(v___x_4493_, 2);
v_postponed_4496_ = lean_ctor_get(v___x_4493_, 3);
v_diag_4497_ = lean_ctor_get(v___x_4493_, 4);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4506_ == 0)
{
lean_object* v_unused_4507_; 
v_unused_4507_ = lean_ctor_get(v___x_4493_, 0);
lean_dec(v_unused_4507_);
v___x_4499_ = v___x_4493_;
v_isShared_4500_ = v_isSharedCheck_4506_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_diag_4497_);
lean_inc(v_postponed_4496_);
lean_inc(v_zetaDeltaFVarIds_4495_);
lean_inc(v_cache_4494_);
lean_dec(v___x_4493_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4506_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v_snd_4492_);
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_snd_4492_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_cache_4494_);
lean_ctor_set(v_reuseFailAlloc_4505_, 2, v_zetaDeltaFVarIds_4495_);
lean_ctor_set(v_reuseFailAlloc_4505_, 3, v_postponed_4496_);
lean_ctor_set(v_reuseFailAlloc_4505_, 4, v_diag_4497_);
v___x_4502_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_st_ref_put(v___y_4484_, v___x_4502_);
v___x_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4504_, 0, v_fst_4491_);
return v___x_4504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg___boxed(lean_object* v_e_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4508_, v___y_4509_);
lean_dec(v___y_4509_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(lean_object* v_e_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4512_, v___y_4514_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___boxed(lean_object* v_e_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(v_e_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(lean_object* v_mvarId_4526_, lean_object* v_x_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4526_, v_x_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
v_a_4542_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4533_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4533_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4550_, lean_object* v_x_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4550_, v_x_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(lean_object* v_00_u03b1_4558_, lean_object* v_mvarId_4559_, lean_object* v_x_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4559_, v_x_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___boxed(lean_object* v_00_u03b1_4567_, lean_object* v_mvarId_4568_, lean_object* v_x_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(v_00_u03b1_4567_, v_mvarId_4568_, v_x_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(lean_object* v___x_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4593_; 
v___x_4582_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v___x_4576_, v___y_4578_);
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4593_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4593_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
uint8_t v___x_4587_; 
v___x_4587_ = l_Lean_Expr_hasSyntheticSorry(v_a_4583_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; 
lean_del_object(v___x_4585_);
v___x_4588_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_a_4583_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
return v___x_4588_;
}
else
{
lean_object* v___x_4589_; lean_object* v___x_4591_; 
lean_dec(v_a_4583_);
v___x_4589_ = lean_box(0);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v___x_4589_);
v___x_4591_ = v___x_4585_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed(lean_object* v___x_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(v___x_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(lean_object* v_mvarId_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v___x_4607_; lean_object* v___f_4608_; lean_object* v___x_4609_; 
lean_inc(v_mvarId_4601_);
v___x_4607_ = l_Lean_mkMVar(v_mvarId_4601_);
v___f_4608_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4608_, 0, v___x_4607_);
v___x_4609_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4601_, v___f_4608_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___boxed(lean_object* v_mvarId_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(lean_object* v_mvarId_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg___boxed(lean_object* v_mvarId_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(v_mvarId_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(lean_object* v_mvarId_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4631_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___boxed(lean_object* v_mvarId_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(v_mvarId_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
lean_object* v_zero_4657_; uint8_t v_isZero_4658_; 
v_zero_4657_ = lean_unsigned_to_nat(0u);
v_isZero_4658_ = lean_nat_dec_eq(v_a_4655_, v_zero_4657_);
if (v_isZero_4658_ == 0)
{
if (lean_obj_tag(v_a_4656_) == 6)
{
lean_object* v_body_4659_; lean_object* v_one_4660_; lean_object* v_n_4661_; 
v_body_4659_ = lean_ctor_get(v_a_4656_, 2);
v_one_4660_ = lean_unsigned_to_nat(1u);
v_n_4661_ = lean_nat_sub(v_a_4655_, v_one_4660_);
lean_dec(v_a_4655_);
v_a_4655_ = v_n_4661_;
v_a_4656_ = v_body_4659_;
goto _start;
}
else
{
lean_dec(v_a_4655_);
lean_inc_ref(v_a_4656_);
return v_a_4656_;
}
}
else
{
lean_dec(v_a_4655_);
lean_inc_ref(v_a_4656_);
return v_a_4656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody___boxed(lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v_a_4663_, v_a_4664_);
lean_dec_ref(v_a_4664_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(lean_object* v_mvarId_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___x_4669_; lean_object* v_mctx_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4669_ = lean_st_ref_get(v___y_4667_);
v_mctx_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc_ref(v_mctx_4670_);
lean_dec(v___x_4669_);
v___x_4671_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_4670_, v_mvarId_4666_);
lean_dec_ref(v_mctx_4670_);
v___x_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg___boxed(lean_object* v_mvarId_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec(v_mvarId_4673_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(lean_object* v_mvarId_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4677_, v___y_4684_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___boxed(lean_object* v_mvarId_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(v_mvarId_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec(v_mvarId_4689_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(lean_object* v_mvarId_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; lean_object* v_mctx_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4704_ = lean_st_ref_get(v___y_4702_);
v_mctx_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc_ref(v_mctx_4705_);
lean_dec(v___x_4704_);
v___x_4706_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_4705_, v_mvarId_4701_);
lean_dec_ref(v_mctx_4705_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg___boxed(lean_object* v_mvarId_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec(v_mvarId_4708_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(lean_object* v_mvarId_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4712_, v___y_4719_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___boxed(lean_object* v_mvarId_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(v_mvarId_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec(v_mvarId_4724_);
return v_res_4735_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(lean_object* v___x_4736_, lean_object* v_x_4737_){
_start:
{
if (lean_obj_tag(v_x_4737_) == 0)
{
uint8_t v___x_4738_; 
v___x_4738_ = 1;
return v___x_4738_;
}
else
{
lean_object* v_head_4739_; lean_object* v_tail_4740_; lean_object* v_fst_4741_; lean_object* v_snd_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v_head_4739_ = lean_ctor_get(v_x_4737_, 0);
v_tail_4740_ = lean_ctor_get(v_x_4737_, 1);
v_fst_4741_ = lean_ctor_get(v_head_4739_, 0);
v_snd_4742_ = lean_ctor_get(v_head_4739_, 1);
v___x_4743_ = lean_unsigned_to_nat(1u);
v___x_4744_ = lean_nat_sub(v___x_4736_, v___x_4743_);
v___x_4745_ = lean_nat_sub(v___x_4744_, v_snd_4742_);
lean_dec(v___x_4744_);
v___x_4746_ = l_Lean_mkBVar(v___x_4745_);
v___x_4747_ = lean_expr_eqv(v_fst_4741_, v___x_4746_);
lean_dec_ref(v___x_4746_);
if (v___x_4747_ == 0)
{
return v___x_4747_;
}
else
{
v_x_4737_ = v_tail_4740_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0___boxed(lean_object* v___x_4749_, lean_object* v_x_4750_){
_start:
{
uint8_t v_res_4751_; lean_object* v_r_4752_; 
v_res_4751_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4749_, v_x_4750_);
lean_dec(v_x_4750_);
lean_dec(v___x_4749_);
v_r_4752_ = lean_box(v_res_4751_);
return v_r_4752_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(lean_object* v_k_4753_, lean_object* v_t_4754_){
_start:
{
if (lean_obj_tag(v_t_4754_) == 0)
{
lean_object* v_k_4755_; lean_object* v_l_4756_; lean_object* v_r_4757_; uint8_t v___x_4758_; 
v_k_4755_ = lean_ctor_get(v_t_4754_, 1);
v_l_4756_ = lean_ctor_get(v_t_4754_, 3);
v_r_4757_ = lean_ctor_get(v_t_4754_, 4);
v___x_4758_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4753_, v_k_4755_);
switch(v___x_4758_)
{
case 0:
{
v_t_4754_ = v_l_4756_;
goto _start;
}
case 1:
{
uint8_t v___x_4760_; 
v___x_4760_ = 1;
return v___x_4760_;
}
default: 
{
v_t_4754_ = v_r_4757_;
goto _start;
}
}
}
else
{
uint8_t v___x_4762_; 
v___x_4762_ = 0;
return v___x_4762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg___boxed(lean_object* v_k_4763_, lean_object* v_t_4764_){
_start:
{
uint8_t v_res_4765_; lean_object* v_r_4766_; 
v_res_4765_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4763_, v_t_4764_);
lean_dec(v_t_4764_);
lean_dec(v_k_4763_);
v_r_4766_ = lean_box(v_res_4765_);
return v_r_4766_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(lean_object* v_a_4767_, lean_object* v_as_4768_, size_t v_i_4769_, size_t v_stop_4770_){
_start:
{
uint8_t v___x_4771_; 
v___x_4771_ = lean_usize_dec_eq(v_i_4769_, v_stop_4770_);
if (v___x_4771_ == 0)
{
lean_object* v_fvars_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; 
v_fvars_4772_ = lean_ctor_get(v_a_4767_, 0);
v___x_4773_ = lean_array_uget_borrowed(v_as_4768_, v_i_4769_);
v___x_4774_ = l_Lean_Expr_fvarId_x21(v___x_4773_);
v___x_4775_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v___x_4774_, v_fvars_4772_);
lean_dec(v___x_4774_);
if (v___x_4775_ == 0)
{
size_t v___x_4776_; size_t v___x_4777_; 
v___x_4776_ = ((size_t)1ULL);
v___x_4777_ = lean_usize_add(v_i_4769_, v___x_4776_);
v_i_4769_ = v___x_4777_;
goto _start;
}
else
{
return v___x_4775_;
}
}
else
{
uint8_t v___x_4779_; 
v___x_4779_ = 0;
return v___x_4779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3___boxed(lean_object* v_a_4780_, lean_object* v_as_4781_, lean_object* v_i_4782_, lean_object* v_stop_4783_){
_start:
{
size_t v_i_boxed_4784_; size_t v_stop_boxed_4785_; uint8_t v_res_4786_; lean_object* v_r_4787_; 
v_i_boxed_4784_ = lean_unbox_usize(v_i_4782_);
lean_dec(v_i_4782_);
v_stop_boxed_4785_ = lean_unbox_usize(v_stop_4783_);
lean_dec(v_stop_4783_);
v_res_4786_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4780_, v_as_4781_, v_i_boxed_4784_, v_stop_boxed_4785_);
lean_dec_ref(v_as_4781_);
lean_dec_ref(v_a_4780_);
v_r_4787_ = lean_box(v_res_4786_);
return v_r_4787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_4788_; lean_object* v_dummy_4789_; 
v___x_4788_ = lean_box(0);
v_dummy_4789_ = l_Lean_Expr_sort___override(v___x_4788_);
return v_dummy_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_mvarId_4790_, lean_object* v_proof_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v_p_4803_; lean_object* v_proof_4806_; lean_object* v___y_4808_; lean_object* v___y_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4884_; lean_object* v___y_4885_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4890_; lean_object* v___y_4891_; lean_object* v___y_4892_; lean_object* v___x_4929_; 
v_proof_4806_ = l_Lean_Expr_headBeta(v_proof_4791_);
v___x_4929_ = l_Lean_Expr_getAppFn(v_proof_4806_);
if (lean_obj_tag(v___x_4929_) == 2)
{
lean_object* v_mvarId_4930_; lean_object* v___x_4931_; 
v_mvarId_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_mvarId_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4930_, v_a_4798_);
lean_dec(v_mvarId_4930_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___x_4931_, 1);
if (lean_obj_tag(v_a_4932_) == 1)
{
lean_object* v_val_4933_; lean_object* v_dummy_4934_; lean_object* v_nargs_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v_val_4933_ = lean_ctor_get(v_a_4932_, 0);
lean_inc(v_val_4933_);
lean_dec_ref_known(v_a_4932_, 1);
v_dummy_4934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4935_ = l_Lean_Expr_getAppNumArgs(v_proof_4806_);
lean_inc(v_nargs_4935_);
v___x_4936_ = lean_mk_array(v_nargs_4935_, v_dummy_4934_);
v___x_4937_ = lean_unsigned_to_nat(1u);
v___x_4938_ = lean_nat_sub(v_nargs_4935_, v___x_4937_);
lean_dec(v_nargs_4935_);
v___x_4939_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_proof_4806_, v___x_4936_, v___x_4938_);
v___x_4940_ = l_Lean_Expr_beta(v_val_4933_, v___x_4939_);
v_proof_4791_ = v___x_4940_;
goto _start;
}
else
{
lean_dec(v_a_4932_);
v___y_4884_ = v_a_4792_;
v___y_4885_ = v_a_4793_;
v___y_4886_ = v_a_4794_;
v___y_4887_ = v_a_4795_;
v___y_4888_ = v_a_4796_;
v___y_4889_ = v_a_4797_;
v___y_4890_ = v_a_4798_;
v___y_4891_ = v_a_4799_;
v___y_4892_ = v_a_4800_;
goto v___jp_4883_;
}
}
else
{
lean_dec_ref(v_proof_4806_);
lean_dec(v_mvarId_4790_);
return v___x_4931_;
}
}
else
{
lean_dec_ref(v___x_4929_);
v___y_4884_ = v_a_4792_;
v___y_4885_ = v_a_4793_;
v___y_4886_ = v_a_4794_;
v___y_4887_ = v_a_4795_;
v___y_4888_ = v_a_4796_;
v___y_4889_ = v_a_4797_;
v___y_4890_ = v_a_4798_;
v___y_4891_ = v_a_4799_;
v___y_4892_ = v_a_4800_;
goto v___jp_4883_;
}
v___jp_4802_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4804_, 0, v_p_4803_);
v___x_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
return v___x_4805_;
}
v___jp_4807_:
{
if (lean_obj_tag(v_proof_4806_) == 6)
{
lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; 
v___x_4817_ = l_Lean_Expr_getNumHeadLambdas(v_proof_4806_);
lean_inc(v___x_4817_);
v___x_4818_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v___x_4817_, v_proof_4806_);
lean_dec_ref_known(v_proof_4806_, 3);
v___x_4819_ = l_Lean_Expr_hasLooseBVars(v___x_4818_);
if (v___x_4819_ == 0)
{
lean_dec(v___x_4817_);
v_proof_4791_ = v___x_4818_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
v_a_4798_ = v___y_4814_;
v_a_4799_ = v___y_4815_;
v_a_4800_ = v___y_4816_;
goto _start;
}
else
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Lean_Expr_getAppFn(v___x_4818_);
if (lean_obj_tag(v___x_4821_) == 2)
{
lean_object* v_mvarId_4822_; lean_object* v_dummy_4823_; lean_object* v_nargs_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_mvarId_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_mvarId_4822_);
lean_dec_ref_known(v___x_4821_, 1);
v_dummy_4823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4824_ = l_Lean_Expr_getAppNumArgs(v___x_4818_);
lean_inc(v_nargs_4824_);
v___x_4825_ = lean_mk_array(v_nargs_4824_, v_dummy_4823_);
v___x_4826_ = lean_unsigned_to_nat(1u);
v___x_4827_ = lean_nat_sub(v_nargs_4824_, v___x_4826_);
lean_dec(v_nargs_4824_);
v___x_4828_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_4818_, v___x_4825_, v___x_4827_);
v___x_4829_ = lean_array_get_size(v___x_4828_);
v___x_4830_ = lean_nat_dec_eq(v___x_4829_, v___x_4817_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; 
lean_dec_ref(v___x_4828_);
lean_dec(v_mvarId_4822_);
lean_dec(v___x_4817_);
v___x_4831_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4790_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
return v___x_4831_;
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v___x_4832_ = lean_array_to_list(v___x_4828_);
v___x_4833_ = lean_unsigned_to_nat(0u);
v___x_4834_ = l_List_zipIdxTR___redArg(v___x_4832_, v___x_4833_);
v___x_4835_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4817_, v___x_4834_);
lean_dec(v___x_4834_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; 
lean_dec(v_mvarId_4822_);
lean_dec(v___x_4817_);
v___x_4836_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4790_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
return v___x_4836_;
}
else
{
lean_object* v___x_4837_; 
v___x_4837_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4822_, v___y_4814_);
lean_dec(v_mvarId_4822_);
if (lean_obj_tag(v___x_4837_) == 0)
{
lean_object* v_a_4838_; 
v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
lean_inc(v_a_4838_);
lean_dec_ref_known(v___x_4837_, 1);
if (lean_obj_tag(v_a_4838_) == 1)
{
lean_object* v_val_4839_; lean_object* v_fvars_4840_; lean_object* v_mvarIdPending_4841_; lean_object* v___x_4842_; uint8_t v___x_4843_; 
v_val_4839_ = lean_ctor_get(v_a_4838_, 0);
lean_inc(v_val_4839_);
lean_dec_ref_known(v_a_4838_, 1);
v_fvars_4840_ = lean_ctor_get(v_val_4839_, 0);
lean_inc_ref(v_fvars_4840_);
v_mvarIdPending_4841_ = lean_ctor_get(v_val_4839_, 1);
lean_inc(v_mvarIdPending_4841_);
lean_dec(v_val_4839_);
v___x_4842_ = lean_array_get_size(v_fvars_4840_);
v___x_4843_ = lean_nat_dec_eq(v___x_4842_, v___x_4817_);
lean_dec(v___x_4817_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; 
lean_dec(v_mvarIdPending_4841_);
lean_dec_ref(v_fvars_4840_);
v___x_4844_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4790_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
return v___x_4844_;
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = l_Lean_mkMVar(v_mvarIdPending_4841_);
lean_inc_ref(v___x_4845_);
v___x_4846_ = l_Lean_Meta_Grind_getProofInfo(v___x_4845_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4862_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4862_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4862_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
uint8_t v___x_4851_; 
v___x_4851_ = lean_nat_dec_lt(v___x_4833_, v___x_4842_);
if (v___x_4851_ == 0)
{
lean_del_object(v___x_4849_);
lean_dec(v_a_4847_);
lean_dec_ref(v_fvars_4840_);
v_proof_4791_ = v___x_4845_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
v_a_4798_ = v___y_4814_;
v_a_4799_ = v___y_4815_;
v_a_4800_ = v___y_4816_;
goto _start;
}
else
{
if (v___x_4851_ == 0)
{
lean_del_object(v___x_4849_);
lean_dec(v_a_4847_);
lean_dec_ref(v_fvars_4840_);
v_proof_4791_ = v___x_4845_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
v_a_4798_ = v___y_4814_;
v_a_4799_ = v___y_4815_;
v_a_4800_ = v___y_4816_;
goto _start;
}
else
{
size_t v___x_4854_; size_t v___x_4855_; uint8_t v___x_4856_; 
v___x_4854_ = ((size_t)0ULL);
v___x_4855_ = lean_usize_of_nat(v___x_4842_);
v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4847_, v_fvars_4840_, v___x_4854_, v___x_4855_);
lean_dec_ref(v_fvars_4840_);
lean_dec(v_a_4847_);
if (v___x_4856_ == 0)
{
lean_del_object(v___x_4849_);
v_proof_4791_ = v___x_4845_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
v_a_4798_ = v___y_4814_;
v_a_4799_ = v___y_4815_;
v_a_4800_ = v___y_4816_;
goto _start;
}
else
{
lean_object* v___x_4858_; lean_object* v___x_4860_; 
lean_dec_ref(v___x_4845_);
lean_dec(v_mvarId_4790_);
v___x_4858_ = lean_box(0);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4858_);
v___x_4860_ = v___x_4849_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v___x_4845_);
lean_dec_ref(v_fvars_4840_);
lean_dec(v_mvarId_4790_);
v_a_4863_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4846_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4846_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
else
{
lean_object* v___x_4871_; 
lean_dec(v_a_4838_);
lean_dec(v___x_4817_);
v___x_4871_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4790_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
return v___x_4871_;
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec(v___x_4817_);
lean_dec(v_mvarId_4790_);
v_a_4872_ = lean_ctor_get(v___x_4837_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4837_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4837_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4837_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
}
}
else
{
lean_object* v___x_4880_; 
lean_dec_ref(v___x_4821_);
lean_dec_ref(v___x_4818_);
lean_dec(v___x_4817_);
v___x_4880_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4790_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
return v___x_4880_;
}
}
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_dec_ref(v_proof_4806_);
lean_dec(v_mvarId_4790_);
v___x_4881_ = lean_box(0);
v___x_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
return v___x_4882_;
}
}
v___jp_4883_:
{
lean_object* v___x_4893_; 
lean_inc_ref(v_proof_4806_);
v___x_4893_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4806_, v___y_4890_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4920_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4896_ = v___x_4893_;
v_isShared_4897_ = v_isSharedCheck_4920_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4920_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4898_; uint8_t v___x_4899_; 
v___x_4898_ = l_Lean_Expr_cleanupAnnotations(v_a_4894_);
lean_dec(v_a_4894_);
v___x_4899_ = l_Lean_Expr_isApp(v___x_4898_);
if (v___x_4899_ == 0)
{
lean_dec_ref(v___x_4898_);
lean_del_object(v___x_4896_);
v___y_4808_ = v___y_4884_;
v___y_4809_ = v___y_4885_;
v___y_4810_ = v___y_4886_;
v___y_4811_ = v___y_4887_;
v___y_4812_ = v___y_4888_;
v___y_4813_ = v___y_4889_;
v___y_4814_ = v___y_4890_;
v___y_4815_ = v___y_4891_;
v___y_4816_ = v___y_4892_;
goto v___jp_4807_;
}
else
{
lean_object* v___x_4900_; uint8_t v___x_4901_; 
v___x_4900_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4898_);
v___x_4901_ = l_Lean_Expr_isApp(v___x_4900_);
if (v___x_4901_ == 0)
{
lean_dec_ref(v___x_4900_);
lean_dec_ref(v___x_4898_);
lean_del_object(v___x_4896_);
v___y_4808_ = v___y_4884_;
v___y_4809_ = v___y_4885_;
v___y_4810_ = v___y_4886_;
v___y_4811_ = v___y_4887_;
v___y_4812_ = v___y_4888_;
v___y_4813_ = v___y_4889_;
v___y_4814_ = v___y_4890_;
v___y_4815_ = v___y_4891_;
v___y_4816_ = v___y_4892_;
goto v___jp_4807_;
}
else
{
lean_object* v_arg_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; uint8_t v___x_4905_; 
v_arg_4902_ = lean_ctor_get(v___x_4898_, 1);
lean_inc_ref(v_arg_4902_);
lean_dec_ref(v___x_4898_);
v___x_4903_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4900_);
v___x_4904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4905_ = l_Lean_Expr_isConstOf(v___x_4903_, v___x_4904_);
if (v___x_4905_ == 0)
{
lean_object* v___x_4906_; uint8_t v___x_4907_; 
lean_dec_ref(v___x_4900_);
lean_del_object(v___x_4896_);
v___x_4906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4907_ = l_Lean_Expr_isConstOf(v___x_4903_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; uint8_t v___x_4909_; 
v___x_4908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4909_ = l_Lean_Expr_isConstOf(v___x_4903_, v___x_4908_);
lean_dec_ref(v___x_4903_);
if (v___x_4909_ == 0)
{
lean_dec_ref(v_arg_4902_);
v___y_4808_ = v___y_4884_;
v___y_4809_ = v___y_4885_;
v___y_4810_ = v___y_4886_;
v___y_4811_ = v___y_4887_;
v___y_4812_ = v___y_4888_;
v___y_4813_ = v___y_4889_;
v___y_4814_ = v___y_4890_;
v___y_4815_ = v___y_4891_;
v___y_4816_ = v___y_4892_;
goto v___jp_4807_;
}
else
{
lean_dec_ref(v_proof_4806_);
lean_dec(v_mvarId_4790_);
v_p_4803_ = v_arg_4902_;
goto v___jp_4802_;
}
}
else
{
lean_dec_ref(v___x_4903_);
lean_dec_ref(v_proof_4806_);
lean_dec(v_mvarId_4790_);
v_p_4803_ = v_arg_4902_;
goto v___jp_4802_;
}
}
else
{
lean_object* v_arg_4910_; uint8_t v___x_4911_; 
lean_dec_ref(v___x_4903_);
lean_dec_ref(v_proof_4806_);
lean_dec(v_mvarId_4790_);
v_arg_4910_ = lean_ctor_get(v___x_4900_, 1);
lean_inc_ref(v_arg_4910_);
lean_dec_ref(v___x_4900_);
v___x_4911_ = l_Lean_Expr_isFalse(v_arg_4910_);
lean_dec_ref(v_arg_4910_);
if (v___x_4911_ == 0)
{
lean_object* v___x_4912_; lean_object* v___x_4914_; 
lean_dec_ref(v_arg_4902_);
v___x_4912_ = lean_box(0);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4912_);
v___x_4914_ = v___x_4896_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4912_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
else
{
lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4916_, 0, v_arg_4902_);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4916_);
v___x_4918_ = v___x_4896_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec_ref(v_proof_4806_);
lean_dec(v_mvarId_4790_);
v_a_4921_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4893_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4893_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_mvarId_4942_, lean_object* v_proof_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_4942_, v_proof_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
return v_res_4954_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(lean_object* v_00_u03b2_4955_, lean_object* v_k_4956_, lean_object* v_t_4957_){
_start:
{
uint8_t v___x_4958_; 
v___x_4958_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4956_, v_t_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_4959_, lean_object* v_k_4960_, lean_object* v_t_4961_){
_start:
{
uint8_t v_res_4962_; lean_object* v_r_4963_; 
v_res_4962_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(v_00_u03b2_4959_, v_k_4960_, v_t_4961_);
lean_dec(v_t_4961_);
lean_dec(v_k_4960_);
v_r_4963_ = lean_box(v_res_4962_);
return v_r_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(lean_object* v_x_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v___x_4975_; 
lean_inc(v___y_4969_);
lean_inc_ref(v___y_4968_);
lean_inc(v___y_4967_);
lean_inc_ref(v___y_4966_);
lean_inc(v___y_4965_);
v___x_4975_ = lean_apply_10(v_x_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, lean_box(0));
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(v_x_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_mvarId_4988_, lean_object* v_x_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v___f_5000_; lean_object* v___x_5001_; 
lean_inc(v___y_4994_);
lean_inc_ref(v___y_4993_);
lean_inc(v___y_4992_);
lean_inc_ref(v___y_4991_);
lean_inc(v___y_4990_);
v___f_5000_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5000_, 0, v_x_4989_);
lean_closure_set(v___f_5000_, 1, v___y_4990_);
lean_closure_set(v___f_5000_, 2, v___y_4991_);
lean_closure_set(v___f_5000_, 3, v___y_4992_);
lean_closure_set(v___f_5000_, 4, v___y_4993_);
lean_closure_set(v___f_5000_, 5, v___y_4994_);
v___x_5001_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4988_, v___f_5000_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_);
if (lean_obj_tag(v___x_5001_) == 0)
{
return v___x_5001_;
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_5010_, lean_object* v_x_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5010_, v_x_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
lean_dec(v___y_5012_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_00_u03b1_5023_, lean_object* v_mvarId_5024_, lean_object* v_x_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v___x_5036_; 
v___x_5036_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5024_, v_x_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_00_u03b1_5037_, lean_object* v_mvarId_5038_, lean_object* v_x_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_00_u03b1_5037_, v_mvarId_5038_, v_x_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v___y_5040_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_5051_, lean_object* v_mvarId_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v___x_5063_; 
lean_inc_ref(v___x_5051_);
v___x_5063_ = l_Lean_Meta_Grind_getProofInfo(v___x_5051_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5076_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5066_ = v___x_5063_;
v_isShared_5067_ = v_isSharedCheck_5076_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5063_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5076_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
uint8_t v_hasSorry_5073_; 
v_hasSorry_5073_ = lean_ctor_get_uint8(v_a_5064_, sizeof(void*)*1);
if (v_hasSorry_5073_ == 0)
{
uint8_t v_hasUnassigned_5074_; 
v_hasUnassigned_5074_ = lean_ctor_get_uint8(v_a_5064_, sizeof(void*)*1 + 1);
lean_dec(v_a_5064_);
if (v_hasUnassigned_5074_ == 0)
{
lean_object* v___x_5075_; 
lean_del_object(v___x_5066_);
v___x_5075_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_5052_, v___x_5051_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
return v___x_5075_;
}
else
{
lean_dec(v_mvarId_5052_);
lean_dec_ref(v___x_5051_);
goto v___jp_5068_;
}
}
else
{
lean_dec(v_a_5064_);
lean_dec(v_mvarId_5052_);
lean_dec_ref(v___x_5051_);
goto v___jp_5068_;
}
v___jp_5068_:
{
lean_object* v___x_5069_; lean_object* v___x_5071_; 
v___x_5069_ = lean_box(0);
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v___x_5069_);
v___x_5071_ = v___x_5066_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_dec(v_mvarId_5052_);
lean_dec_ref(v___x_5051_);
v_a_5077_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5063_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5063_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_5085_, lean_object* v_mvarId_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_5085_, v_mvarId_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v___x_5109_; lean_object* v___f_5110_; lean_object* v___x_5111_; 
lean_inc_n(v_mvarId_5098_, 2);
v___x_5109_ = l_Lean_mkMVar(v_mvarId_5098_);
v___f_5110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5110_, 0, v___x_5109_);
lean_closure_set(v___f_5110_, 1, v_mvarId_5098_);
v___x_5111_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5098_, v___f_5110_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_);
lean_dec(v_a_5121_);
lean_dec_ref(v_a_5120_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
lean_dec(v_a_5117_);
lean_dec_ref(v_a_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
lean_dec(v_a_5113_);
return v_res_5123_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_5145_){
_start:
{
if (lean_obj_tag(v_x_5145_) == 0)
{
uint8_t v___x_5146_; 
v___x_5146_ = 1;
return v___x_5146_;
}
else
{
lean_object* v_head_5147_; lean_object* v_tail_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; 
v_head_5147_ = lean_ctor_get(v_x_5145_, 0);
lean_inc_n(v_head_5147_, 2);
v_tail_5148_ = lean_ctor_get(v_x_5145_, 1);
lean_inc(v_tail_5148_);
lean_dec_ref_known(v_x_5145_, 2);
v___x_5149_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_5150_ = l_Lean_Syntax_isOfKind(v_head_5147_, v___x_5149_);
if (v___x_5150_ == 0)
{
lean_object* v___x_5151_; uint8_t v___x_5152_; 
v___x_5151_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_5147_);
v___x_5152_ = l_Lean_Syntax_isOfKind(v_head_5147_, v___x_5151_);
if (v___x_5152_ == 0)
{
lean_dec(v_head_5147_);
v_x_5145_ = v_tail_5148_;
goto _start;
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; uint8_t v___x_5157_; 
v___x_5154_ = lean_unsigned_to_nat(1u);
v___x_5155_ = l_Lean_Syntax_getArg(v_head_5147_, v___x_5154_);
lean_dec(v_head_5147_);
v___x_5156_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5157_ = l_Lean_Syntax_isOfKind(v___x_5155_, v___x_5156_);
if (v___x_5157_ == 0)
{
v_x_5145_ = v_tail_5148_;
goto _start;
}
else
{
lean_dec(v_tail_5148_);
return v___x_5150_;
}
}
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; 
v___x_5159_ = lean_unsigned_to_nat(3u);
v___x_5160_ = l_Lean_Syntax_getArg(v_head_5147_, v___x_5159_);
lean_dec(v_head_5147_);
v___x_5161_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5162_ = l_Lean_Syntax_isOfKind(v___x_5160_, v___x_5161_);
if (v___x_5162_ == 0)
{
v_x_5145_ = v_tail_5148_;
goto _start;
}
else
{
uint8_t v___x_5164_; 
lean_dec(v_tail_5148_);
v___x_5164_ = 0;
return v___x_5164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_5165_){
_start:
{
uint8_t v_res_5166_; lean_object* v_r_5167_; 
v_res_5166_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_5165_);
v_r_5167_ = lean_box(v_res_5166_);
return v_r_5167_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_5168_){
_start:
{
uint8_t v___x_5169_; 
v___x_5169_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_5168_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_5170_){
_start:
{
uint8_t v_res_5171_; lean_object* v_r_5172_; 
v_res_5171_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_5170_);
v_r_5172_ = lean_box(v_res_5171_);
return v_r_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_5188_, lean_object* v_a_5189_){
_start:
{
if (lean_obj_tag(v_seq_5188_) == 0)
{
lean_object* v_ref_5191_; uint8_t v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v_ref_5191_ = lean_ctor_get(v_a_5189_, 2);
v___x_5192_ = 0;
v___x_5193_ = l_Lean_SourceInfo_fromRef(v_ref_5191_, v___x_5192_);
v___x_5194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_5195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_5193_);
v___x_5196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5193_);
lean_ctor_set(v___x_5196_, 1, v___x_5194_);
v___x_5197_ = l_Lean_Syntax_node1(v___x_5193_, v___x_5195_, v___x_5196_);
v___x_5198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
return v___x_5198_;
}
else
{
lean_object* v_tail_5199_; 
v_tail_5199_ = lean_ctor_get(v_seq_5188_, 1);
if (lean_obj_tag(v_tail_5199_) == 0)
{
lean_object* v_head_5200_; lean_object* v___x_5201_; 
v_head_5200_ = lean_ctor_get(v_seq_5188_, 0);
lean_inc(v_head_5200_);
lean_dec_ref_known(v_seq_5188_, 2);
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v_head_5200_);
return v___x_5201_;
}
else
{
lean_object* v_head_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5224_; 
lean_inc(v_tail_5199_);
v_head_5202_ = lean_ctor_get(v_seq_5188_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v_seq_5188_);
if (v_isSharedCheck_5224_ == 0)
{
lean_object* v_unused_5225_; 
v_unused_5225_ = lean_ctor_get(v_seq_5188_, 1);
lean_dec(v_unused_5225_);
v___x_5204_ = v_seq_5188_;
v_isShared_5205_ = v_isSharedCheck_5224_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_head_5202_);
lean_dec(v_seq_5188_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5224_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5206_; lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5223_; 
v___x_5206_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_5199_, v_a_5189_);
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5209_ = v___x_5206_;
v_isShared_5210_ = v_isSharedCheck_5223_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5206_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5223_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v_ref_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5217_; 
v_ref_5211_ = lean_ctor_get(v_a_5189_, 2);
v___x_5212_ = 0;
v___x_5213_ = l_Lean_SourceInfo_fromRef(v_ref_5211_, v___x_5212_);
v___x_5214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5213_);
if (v_isShared_5205_ == 0)
{
lean_ctor_set_tag(v___x_5204_, 2);
lean_ctor_set(v___x_5204_, 1, v___x_5215_);
lean_ctor_set(v___x_5204_, 0, v___x_5213_);
v___x_5217_ = v___x_5204_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5222_, 1, v___x_5215_);
v___x_5217_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
lean_object* v___x_5218_; lean_object* v___x_5220_; 
v___x_5218_ = l_Lean_Syntax_node3(v___x_5213_, v___x_5214_, v_head_5202_, v___x_5217_, v_a_5207_);
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 0, v___x_5218_);
v___x_5220_ = v___x_5209_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v___x_5218_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5226_, v_a_5227_);
lean_dec_ref(v_a_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v___x_5234_; 
v___x_5234_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5230_, v_a_5231_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_5235_, v_a_5236_, v_a_5237_);
lean_dec(v_a_5237_);
lean_dec_ref(v_a_5236_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_5240_, lean_object* v_seq_5241_, lean_object* v_a_5242_){
_start:
{
if (lean_obj_tag(v_seq_5241_) == 0)
{
lean_object* v___x_5244_; 
v___x_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5244_, 0, v_cases_5240_);
return v___x_5244_;
}
else
{
lean_object* v___x_5245_; lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5260_; 
v___x_5245_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5241_, v_a_5242_);
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5248_ = v___x_5245_;
v_isShared_5249_ = v_isSharedCheck_5260_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5260_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v_ref_5250_; uint8_t v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5258_; 
v_ref_5250_ = lean_ctor_get(v_a_5242_, 2);
v___x_5251_ = 0;
v___x_5252_ = l_Lean_SourceInfo_fromRef(v_ref_5250_, v___x_5251_);
v___x_5253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5252_);
v___x_5255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5252_);
lean_ctor_set(v___x_5255_, 1, v___x_5254_);
v___x_5256_ = l_Lean_Syntax_node3(v___x_5252_, v___x_5253_, v_cases_5240_, v___x_5255_, v_a_5246_);
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 0, v___x_5256_);
v___x_5258_ = v___x_5248_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5256_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_5261_, lean_object* v_seq_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5261_, v_seq_5262_, v_a_5263_);
lean_dec_ref(v_a_5263_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_5266_, lean_object* v_seq_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_){
_start:
{
lean_object* v___x_5271_; 
v___x_5271_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5266_, v_seq_5267_, v_a_5268_);
return v___x_5271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_5272_, lean_object* v_seq_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_5272_, v_seq_5273_, v_a_5274_, v_a_5275_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
return v_res_5277_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_5278_, lean_object* v_x_5279_){
_start:
{
if (lean_obj_tag(v_x_5278_) == 0)
{
if (lean_obj_tag(v_x_5279_) == 0)
{
uint8_t v___x_5280_; 
v___x_5280_ = 1;
return v___x_5280_;
}
else
{
uint8_t v___x_5281_; 
v___x_5281_ = 0;
return v___x_5281_;
}
}
else
{
if (lean_obj_tag(v_x_5279_) == 0)
{
uint8_t v___x_5282_; 
v___x_5282_ = 0;
return v___x_5282_;
}
else
{
lean_object* v_head_5283_; lean_object* v_tail_5284_; lean_object* v_head_5285_; lean_object* v_tail_5286_; uint8_t v___x_5287_; 
v_head_5283_ = lean_ctor_get(v_x_5278_, 0);
v_tail_5284_ = lean_ctor_get(v_x_5278_, 1);
v_head_5285_ = lean_ctor_get(v_x_5279_, 0);
v_tail_5286_ = lean_ctor_get(v_x_5279_, 1);
v___x_5287_ = l_Lean_Syntax_structEq(v_head_5283_, v_head_5285_);
if (v___x_5287_ == 0)
{
return v___x_5287_;
}
else
{
v_x_5278_ = v_tail_5284_;
v_x_5279_ = v_tail_5286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_5289_, lean_object* v_x_5290_){
_start:
{
uint8_t v_res_5291_; lean_object* v_r_5292_; 
v_res_5291_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_5289_, v_x_5290_);
lean_dec(v_x_5290_);
lean_dec(v_x_5289_);
v_r_5292_ = lean_box(v_res_5291_);
return v_r_5292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_5293_, lean_object* v___x_5294_, lean_object* v_as_5295_, size_t v_i_5296_, size_t v_stop_5297_){
_start:
{
uint8_t v___x_5302_; 
v___x_5302_ = lean_usize_dec_eq(v_i_5296_, v_stop_5297_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5303_; uint8_t v___x_5304_; 
v___x_5303_ = lean_array_uget_borrowed(v_as_5295_, v_i_5296_);
v___x_5304_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_5303_, v_alt_5293_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; uint8_t v___x_5306_; 
v___x_5305_ = lean_unsigned_to_nat(0u);
v___x_5306_ = lean_nat_dec_lt(v___x_5305_, v___x_5294_);
if (v___x_5306_ == 0)
{
goto v___jp_5298_;
}
else
{
return v___x_5306_;
}
}
else
{
goto v___jp_5298_;
}
}
else
{
uint8_t v___x_5307_; 
v___x_5307_ = 0;
return v___x_5307_;
}
v___jp_5298_:
{
size_t v___x_5299_; size_t v___x_5300_; 
v___x_5299_ = ((size_t)1ULL);
v___x_5300_ = lean_usize_add(v_i_5296_, v___x_5299_);
v_i_5296_ = v___x_5300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_5308_, lean_object* v___x_5309_, lean_object* v_as_5310_, lean_object* v_i_5311_, lean_object* v_stop_5312_){
_start:
{
size_t v_i_boxed_5313_; size_t v_stop_boxed_5314_; uint8_t v_res_5315_; lean_object* v_r_5316_; 
v_i_boxed_5313_ = lean_unbox_usize(v_i_5311_);
lean_dec(v_i_5311_);
v_stop_boxed_5314_ = lean_unbox_usize(v_stop_5312_);
lean_dec(v_stop_5312_);
v_res_5315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5308_, v___x_5309_, v_as_5310_, v_i_boxed_5313_, v_stop_boxed_5314_);
lean_dec_ref(v_as_5310_);
lean_dec(v___x_5309_);
lean_dec(v_alt_5308_);
v_r_5316_ = lean_box(v_res_5315_);
return v_r_5316_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_5317_){
_start:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; uint8_t v___x_5320_; 
v___x_5318_ = lean_unsigned_to_nat(0u);
v___x_5319_ = lean_array_get_size(v_alts_5317_);
v___x_5320_ = lean_nat_dec_lt(v___x_5318_, v___x_5319_);
if (v___x_5320_ == 0)
{
uint8_t v___x_5321_; 
v___x_5321_ = 1;
return v___x_5321_;
}
else
{
lean_object* v_alt_5322_; uint8_t v___x_5323_; 
v_alt_5322_ = lean_array_fget_borrowed(v_alts_5317_, v___x_5318_);
lean_inc(v_alt_5322_);
v___x_5323_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_5322_);
if (v___x_5323_ == 0)
{
return v___x_5323_;
}
else
{
if (v___x_5320_ == 0)
{
return v___x_5320_;
}
else
{
size_t v___x_5324_; size_t v___x_5325_; uint8_t v___x_5326_; 
v___x_5324_ = ((size_t)0ULL);
v___x_5325_ = lean_usize_of_nat(v___x_5319_);
v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5322_, v___x_5319_, v_alts_5317_, v___x_5324_, v___x_5325_);
if (v___x_5326_ == 0)
{
return v___x_5320_;
}
else
{
uint8_t v___x_5327_; 
v___x_5327_ = 0;
return v___x_5327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_5328_){
_start:
{
uint8_t v_res_5329_; lean_object* v_r_5330_; 
v_res_5329_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5328_);
lean_dec_ref(v_alts_5328_);
v_r_5330_ = lean_box(v_res_5329_);
return v_r_5330_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_5338_){
_start:
{
if (lean_obj_tag(v_alt_5338_) == 1)
{
lean_object* v_tail_5339_; 
v_tail_5339_ = lean_ctor_get(v_alt_5338_, 1);
if (lean_obj_tag(v_tail_5339_) == 0)
{
lean_object* v_head_5340_; lean_object* v___x_5341_; uint8_t v___x_5342_; 
v_head_5340_ = lean_ctor_get(v_alt_5338_, 0);
lean_inc(v_head_5340_);
lean_dec_ref_known(v_alt_5338_, 2);
v___x_5341_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_5342_ = l_Lean_Syntax_isOfKind(v_head_5340_, v___x_5341_);
return v___x_5342_;
}
else
{
uint8_t v___x_5343_; 
lean_dec_ref_known(v_alt_5338_, 2);
v___x_5343_ = 0;
return v___x_5343_;
}
}
else
{
uint8_t v___x_5344_; 
lean_dec(v_alt_5338_);
v___x_5344_ = 0;
return v___x_5344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_5345_){
_start:
{
uint8_t v_res_5346_; lean_object* v_r_5347_; 
v_res_5346_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_5345_);
v_r_5347_ = lean_box(v_res_5346_);
return v_r_5347_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_5348_, lean_object* v_x_5349_, lean_object* v___y_5350_){
_start:
{
if (lean_obj_tag(v_x_5348_) == 0)
{
lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5352_ = l_List_reverse___redArg(v_x_5349_);
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5352_);
return v___x_5353_;
}
else
{
lean_object* v_head_5354_; lean_object* v_tail_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5373_; 
v_head_5354_ = lean_ctor_get(v_x_5348_, 0);
v_tail_5355_ = lean_ctor_get(v_x_5348_, 1);
v_isSharedCheck_5373_ = !lean_is_exclusive(v_x_5348_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5357_ = v_x_5348_;
v_isShared_5358_ = v_isSharedCheck_5373_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_tail_5355_);
lean_inc(v_head_5354_);
lean_dec(v_x_5348_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5373_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; 
v___x_5359_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_5354_, v___y_5350_);
if (lean_obj_tag(v___x_5359_) == 0)
{
lean_object* v_a_5360_; lean_object* v___x_5362_; 
v_a_5360_ = lean_ctor_get(v___x_5359_, 0);
lean_inc(v_a_5360_);
lean_dec_ref_known(v___x_5359_, 1);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v_x_5349_);
lean_ctor_set(v___x_5357_, 0, v_a_5360_);
v___x_5362_ = v___x_5357_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5360_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v_x_5349_);
v___x_5362_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
v_x_5348_ = v_tail_5355_;
v_x_5349_ = v___x_5362_;
goto _start;
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_del_object(v___x_5357_);
lean_dec(v_tail_5355_);
lean_dec(v_x_5349_);
v_a_5365_ = lean_ctor_get(v___x_5359_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5359_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5359_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_5374_, lean_object* v_x_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5374_, v_x_5375_, v___y_5376_);
lean_dec_ref(v___y_5376_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_5379_, lean_object* v_alts_5380_, uint8_t v_compress_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_){
_start:
{
lean_object* v_seq_5386_; 
if (v_compress_5381_ == 0)
{
goto v___jp_5389_;
}
else
{
uint8_t v___x_5399_; 
v___x_5399_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5380_);
if (v___x_5399_ == 0)
{
goto v___jp_5389_;
}
else
{
lean_object* v___x_5400_; lean_object* v___x_5401_; uint8_t v___x_5402_; 
v___x_5400_ = lean_unsigned_to_nat(0u);
v___x_5401_ = lean_array_get_size(v_alts_5380_);
v___x_5402_ = lean_nat_dec_lt(v___x_5400_, v___x_5401_);
if (v___x_5402_ == 0)
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
lean_dec_ref(v_alts_5380_);
v___x_5403_ = lean_box(0);
v___x_5404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5404_, 0, v_cases_5379_);
lean_ctor_set(v___x_5404_, 1, v___x_5403_);
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5404_);
return v___x_5405_;
}
else
{
lean_object* v___x_5406_; lean_object* v_firstAlt_5407_; uint8_t v___x_5408_; 
v___x_5406_ = lean_box(0);
v_firstAlt_5407_ = lean_array_get(v___x_5406_, v_alts_5380_, v___x_5400_);
lean_dec_ref(v_alts_5380_);
lean_inc(v_firstAlt_5407_);
v___x_5408_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_5407_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5418_; 
v___x_5409_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5379_, v_firstAlt_5407_, v_a_5382_);
v_a_5410_ = lean_ctor_get(v___x_5409_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5409_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5412_ = v___x_5409_;
v_isShared_5413_ = v_isSharedCheck_5418_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___x_5409_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5418_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5414_; lean_object* v___x_5416_; 
v___x_5414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5414_, 0, v_a_5410_);
lean_ctor_set(v___x_5414_, 1, v___x_5406_);
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 0, v___x_5414_);
v___x_5416_ = v___x_5412_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5414_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
}
else
{
lean_object* v___x_5419_; 
lean_dec(v_cases_5379_);
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v_firstAlt_5407_);
return v___x_5419_;
}
}
}
}
v___jp_5385_:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5387_, 0, v_cases_5379_);
lean_ctor_set(v___x_5387_, 1, v_seq_5386_);
v___x_5388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5387_);
return v___x_5388_;
}
v___jp_5389_:
{
lean_object* v___x_5390_; lean_object* v___x_5391_; uint8_t v___x_5392_; 
v___x_5390_ = lean_array_get_size(v_alts_5380_);
v___x_5391_ = lean_unsigned_to_nat(1u);
v___x_5392_ = lean_nat_dec_eq(v___x_5390_, v___x_5391_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5393_ = lean_array_to_list(v_alts_5380_);
v___x_5394_ = lean_box(0);
v___x_5395_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_5393_, v___x_5394_, v_a_5382_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_a_5396_; 
v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_a_5396_);
lean_dec_ref_known(v___x_5395_, 1);
v_seq_5386_ = v_a_5396_;
goto v___jp_5385_;
}
else
{
lean_dec(v_cases_5379_);
return v___x_5395_;
}
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5397_ = lean_unsigned_to_nat(0u);
v___x_5398_ = lean_array_fget(v_alts_5380_, v___x_5397_);
lean_dec_ref(v_alts_5380_);
v_seq_5386_ = v___x_5398_;
goto v___jp_5385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_5420_, lean_object* v_alts_5421_, lean_object* v_compress_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_){
_start:
{
uint8_t v_compress_boxed_5426_; lean_object* v_res_5427_; 
v_compress_boxed_5426_ = lean_unbox(v_compress_5422_);
v_res_5427_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_5420_, v_alts_5421_, v_compress_boxed_5426_, v_a_5423_, v_a_5424_);
lean_dec(v_a_5424_);
lean_dec_ref(v_a_5423_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_5428_, lean_object* v_x_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5428_, v_x_5429_, v___y_5430_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_5434_, lean_object* v_x_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_5434_, v_x_5435_, v___y_5436_, v___y_5437_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_5440_, lean_object* v___y_5441_){
_start:
{
lean_object* v___x_5443_; lean_object* v_env_5444_; uint8_t v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5443_ = lean_st_ref_get(v___y_5441_);
v_env_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc_ref(v_env_5444_);
lean_dec(v___x_5443_);
v___x_5445_ = l_Lean_Meta_isMatcherAppCore(v_env_5444_, v_e_5440_);
v___x_5446_ = lean_box(v___x_5445_);
v___x_5447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5447_, 0, v___x_5446_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5448_, v___y_5449_);
lean_dec(v___y_5449_);
lean_dec_ref(v_e_5448_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5452_, v___y_5462_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_res_5477_; 
v_res_5477_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec(v___y_5466_);
lean_dec_ref(v_e_5465_);
return v_res_5477_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5479_; lean_object* v___x_5480_; 
v___x_5479_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5480_ = l_Lean_stringToMessageData(v___x_5479_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5481_, lean_object* v_c_5482_, lean_object* v_a_5483_, lean_object* v_numCases_5484_, uint8_t v_isRec_5485_, lean_object* v_anchorInfo_x3f_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_){
_start:
{
lean_object* v_mvarIds_5499_; lean_object* v___x_5549_; 
v___x_5549_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5481_, v___y_5487_);
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v___y_5552_; lean_object* v___x_5604_; uint8_t v___x_5607_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
lean_inc(v_a_5550_);
lean_dec_ref_known(v___x_5549_, 1);
v___x_5604_ = lean_unsigned_to_nat(1u);
v___x_5607_ = lean_nat_dec_lt(v___x_5604_, v_numCases_5484_);
if (v___x_5607_ == 0)
{
if (v_isRec_5485_ == 0)
{
lean_inc(v_a_5550_);
v___y_5552_ = v_a_5550_;
goto v___jp_5551_;
}
else
{
goto v___jp_5605_;
}
}
else
{
goto v___jp_5605_;
}
v___jp_5551_:
{
lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5553_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5482_);
lean_inc_ref(v___x_5481_);
v___x_5554_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5481_, v___y_5552_, v_numCases_5484_, v___x_5553_, v___y_5490_, v___y_5493_, v___y_5495_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v___x_5555_; 
lean_dec_ref_known(v___x_5554_, 1);
lean_inc_ref(v___x_5481_);
v___x_5555_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5481_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5555_) == 0)
{
lean_object* v_toCold_5556_; lean_object* v_options_5557_; uint8_t v_hasTrace_5558_; 
lean_dec_ref_known(v___x_5555_, 1);
v_toCold_5556_ = lean_ctor_get(v___y_5495_, 0);
v_options_5557_ = lean_ctor_get(v_toCold_5556_, 2);
v_hasTrace_5558_ = lean_ctor_get_uint8(v_options_5557_, sizeof(void*)*1);
if (v_hasTrace_5558_ == 0)
{
lean_dec(v_a_5550_);
goto v___jp_5502_;
}
else
{
lean_object* v_inheritedTraceOptions_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; uint8_t v___x_5562_; 
v_inheritedTraceOptions_5559_ = lean_ctor_get(v_toCold_5556_, 11);
v___x_5560_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5561_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5559_, v_options_5557_, v___x_5561_);
if (v___x_5562_ == 0)
{
lean_dec(v_a_5550_);
goto v___jp_5502_;
}
else
{
lean_object* v___x_5563_; 
v___x_5563_ = l_Lean_Meta_Grind_updateLastTag(v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; 
lean_dec_ref_known(v___x_5563_, 1);
lean_inc_ref(v___x_5481_);
v___x_5564_ = l_Lean_MessageData_ofExpr(v___x_5481_);
v___x_5565_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5564_);
lean_ctor_set(v___x_5566_, 1, v___x_5565_);
v___x_5567_ = l_Nat_reprFast(v_a_5550_);
v___x_5568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
v___x_5569_ = l_Lean_MessageData_ofFormat(v___x_5568_);
v___x_5570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5566_);
lean_ctor_set(v___x_5570_, 1, v___x_5569_);
v___x_5571_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5560_, v___x_5570_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_dec_ref_known(v___x_5571_, 1);
goto v___jp_5502_;
}
else
{
lean_object* v_a_5572_; lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5579_; 
lean_dec(v_anchorInfo_x3f_5486_);
lean_dec(v_a_5483_);
lean_dec_ref(v_c_5482_);
lean_dec_ref(v___x_5481_);
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5574_ = v___x_5571_;
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
else
{
lean_inc(v_a_5572_);
lean_dec(v___x_5571_);
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
else
{
lean_object* v_a_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5587_; 
lean_dec(v_a_5550_);
lean_dec(v_anchorInfo_x3f_5486_);
lean_dec(v_a_5483_);
lean_dec_ref(v_c_5482_);
lean_dec_ref(v___x_5481_);
v_a_5580_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5582_ = v___x_5563_;
v_isShared_5583_ = v_isSharedCheck_5587_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_a_5580_);
lean_dec(v___x_5563_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5587_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5585_; 
if (v_isShared_5583_ == 0)
{
v___x_5585_ = v___x_5582_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
}
}
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
lean_dec(v_a_5550_);
lean_dec(v_anchorInfo_x3f_5486_);
lean_dec(v_a_5483_);
lean_dec_ref(v_c_5482_);
lean_dec_ref(v___x_5481_);
v_a_5588_ = lean_ctor_get(v___x_5555_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5555_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5590_ = v___x_5555_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5555_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5603_; 
lean_dec(v_a_5550_);
lean_dec(v_anchorInfo_x3f_5486_);
lean_dec(v_a_5483_);
lean_dec_ref(v_c_5482_);
lean_dec_ref(v___x_5481_);
v_a_5596_ = lean_ctor_get(v___x_5554_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5598_ = v___x_5554_;
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5554_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
v___jp_5605_:
{
lean_object* v___x_5606_; 
v___x_5606_ = lean_nat_add(v_a_5550_, v___x_5604_);
v___y_5552_ = v___x_5606_;
goto v___jp_5551_;
}
}
else
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5615_; 
lean_dec(v_anchorInfo_x3f_5486_);
lean_dec(v_numCases_5484_);
lean_dec(v_a_5483_);
lean_dec_ref(v_c_5482_);
lean_dec_ref(v___x_5481_);
v_a_5608_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5610_ = v___x_5549_;
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5549_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5613_; 
if (v_isShared_5611_ == 0)
{
v___x_5613_ = v___x_5610_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5608_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
v___jp_5498_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; 
v___x_5500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5500_, 0, v_mvarIds_5499_);
lean_ctor_set(v___x_5500_, 1, v_anchorInfo_x3f_5486_);
v___x_5501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5501_, 0, v___x_5500_);
return v___x_5501_;
}
v___jp_5502_:
{
lean_object* v___x_5503_; 
v___x_5503_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5481_, v___y_5496_);
if (lean_obj_tag(v_c_5482_) == 1)
{
lean_object* v_e_5504_; lean_object* v_binderType_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; 
lean_dec_ref(v___x_5503_);
lean_dec_ref(v___x_5481_);
v_e_5504_ = lean_ctor_get(v_c_5482_, 0);
lean_inc_ref(v_e_5504_);
lean_dec_ref_known(v_c_5482_, 2);
v_binderType_5505_ = lean_ctor_get(v_e_5504_, 1);
lean_inc_ref(v_binderType_5505_);
lean_dec_ref(v_e_5504_);
v___x_5506_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5505_);
v___x_5507_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5483_, v___x_5506_, v___y_5489_, v___y_5490_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref_known(v___x_5507_, 1);
v_mvarIds_5499_ = v_a_5508_;
goto v___jp_5498_;
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5516_; 
lean_dec(v_anchorInfo_x3f_5486_);
v_a_5509_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5511_ = v___x_5507_;
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5507_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
if (v_isShared_5512_ == 0)
{
v___x_5514_ = v___x_5511_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
}
}
}
}
else
{
lean_object* v_a_5517_; uint8_t v___x_5518_; 
lean_dec_ref(v_c_5482_);
v_a_5517_ = lean_ctor_get(v___x_5503_, 0);
lean_inc(v_a_5517_);
lean_dec_ref(v___x_5503_);
v___x_5518_ = lean_unbox(v_a_5517_);
lean_dec(v_a_5517_);
if (v___x_5518_ == 0)
{
lean_object* v___x_5519_; 
v___x_5519_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5481_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5519_) == 0)
{
lean_object* v_a_5520_; lean_object* v___x_5521_; 
v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
lean_inc(v_a_5520_);
lean_dec_ref_known(v___x_5519_, 1);
v___x_5521_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5483_, v_a_5520_, v___y_5489_, v___y_5490_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc(v_a_5522_);
lean_dec_ref_known(v___x_5521_, 1);
v_mvarIds_5499_ = v_a_5522_;
goto v___jp_5498_;
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
lean_dec(v_anchorInfo_x3f_5486_);
v_a_5523_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v___x_5521_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v___x_5521_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec(v_anchorInfo_x3f_5486_);
lean_dec(v_a_5483_);
v_a_5531_ = lean_ctor_get(v___x_5519_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5519_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5519_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
else
{
lean_object* v___x_5539_; 
v___x_5539_ = l_Lean_Meta_Grind_casesMatch(v_a_5483_, v___x_5481_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
if (lean_obj_tag(v___x_5539_) == 0)
{
lean_object* v_a_5540_; 
v_a_5540_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_a_5540_);
lean_dec_ref_known(v___x_5539_, 1);
v_mvarIds_5499_ = v_a_5540_;
goto v___jp_5498_;
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_dec(v_anchorInfo_x3f_5486_);
v_a_5541_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5539_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5539_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5616_ = _args[0];
lean_object* v_c_5617_ = _args[1];
lean_object* v_a_5618_ = _args[2];
lean_object* v_numCases_5619_ = _args[3];
lean_object* v_isRec_5620_ = _args[4];
lean_object* v_anchorInfo_x3f_5621_ = _args[5];
lean_object* v___y_5622_ = _args[6];
lean_object* v___y_5623_ = _args[7];
lean_object* v___y_5624_ = _args[8];
lean_object* v___y_5625_ = _args[9];
lean_object* v___y_5626_ = _args[10];
lean_object* v___y_5627_ = _args[11];
lean_object* v___y_5628_ = _args[12];
lean_object* v___y_5629_ = _args[13];
lean_object* v___y_5630_ = _args[14];
lean_object* v___y_5631_ = _args[15];
lean_object* v___y_5632_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5633_; lean_object* v_res_5634_; 
v_isRec_boxed_5633_ = lean_unbox(v_isRec_5620_);
v_res_5634_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5616_, v_c_5617_, v_a_5618_, v_numCases_5619_, v_isRec_boxed_5633_, v_anchorInfo_x3f_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
lean_dec(v___y_5625_);
lean_dec_ref(v___y_5624_);
lean_dec(v___y_5623_);
lean_dec(v___y_5622_);
return v_res_5634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5635_, uint8_t v_trace_5636_, lean_object* v___f_5637_, lean_object* v_c_5638_, lean_object* v_candidates_x3f_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_){
_start:
{
lean_object* v___x_5650_; lean_object* v___y_5652_; 
v___x_5650_ = lean_st_mk_ref(v_goal_5635_);
if (v_trace_5636_ == 0)
{
lean_object* v___x_5671_; lean_object* v___x_5672_; 
lean_dec(v_candidates_x3f_5639_);
v___x_5671_ = lean_box(0);
lean_inc(v___x_5650_);
v___x_5672_ = lean_apply_12(v___f_5637_, v___x_5671_, v___x_5650_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, lean_box(0));
v___y_5652_ = v___x_5672_;
goto v___jp_5651_;
}
else
{
lean_object* v___x_5673_; 
v___x_5673_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5638_, v_candidates_x3f_5639_, v___x_5650_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v_a_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v_a_5674_ = lean_ctor_get(v___x_5673_, 0);
lean_inc(v_a_5674_);
lean_dec_ref_known(v___x_5673_, 1);
v___x_5675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5675_, 0, v_a_5674_);
lean_inc(v___x_5650_);
v___x_5676_ = lean_apply_12(v___f_5637_, v___x_5675_, v___x_5650_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, lean_box(0));
v___y_5652_ = v___x_5676_;
goto v___jp_5651_;
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5684_; 
lean_dec(v___x_5650_);
lean_dec(v___y_5648_);
lean_dec_ref(v___y_5647_);
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___f_5637_);
v_a_5677_ = lean_ctor_get(v___x_5673_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5679_ = v___x_5673_;
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5673_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5680_ == 0)
{
v___x_5682_ = v___x_5679_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
v___jp_5651_:
{
if (lean_obj_tag(v___y_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5662_; 
v_a_5653_ = lean_ctor_get(v___y_5652_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___y_5652_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5655_ = v___y_5652_;
v_isShared_5656_ = v_isSharedCheck_5662_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___y_5652_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5662_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5660_; 
v___x_5657_ = lean_st_ref_get(v___x_5650_);
lean_dec(v___x_5650_);
v___x_5658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5658_, 0, v_a_5653_);
lean_ctor_set(v___x_5658_, 1, v___x_5657_);
if (v_isShared_5656_ == 0)
{
lean_ctor_set(v___x_5655_, 0, v___x_5658_);
v___x_5660_ = v___x_5655_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5658_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
}
}
}
else
{
lean_object* v_a_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5670_; 
lean_dec(v___x_5650_);
v_a_5663_ = lean_ctor_get(v___y_5652_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___y_5652_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5665_ = v___y_5652_;
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_a_5663_);
lean_dec(v___y_5652_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5668_; 
if (v_isShared_5666_ == 0)
{
v___x_5668_ = v___x_5665_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5685_, lean_object* v_trace_5686_, lean_object* v___f_5687_, lean_object* v_c_5688_, lean_object* v_candidates_x3f_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_){
_start:
{
uint8_t v_trace_boxed_5700_; lean_object* v_res_5701_; 
v_trace_boxed_5700_ = lean_unbox(v_trace_5686_);
v_res_5701_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5685_, v_trace_boxed_5700_, v___f_5687_, v_c_5688_, v_candidates_x3f_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_);
lean_dec_ref(v_c_5688_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object* v_snd_5702_, lean_object* v_a_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
lean_object* v___x_5714_; 
v___x_5714_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5702_, v___y_5706_);
if (lean_obj_tag(v___x_5714_) == 0)
{
lean_object* v_a_5715_; lean_object* v___x_5716_; 
v_a_5715_ = lean_ctor_get(v___x_5714_, 0);
lean_inc(v_a_5715_);
lean_dec_ref_known(v___x_5714_, 1);
lean_inc(v_a_5703_);
v___x_5716_ = l_Lean_MVarId_getType(v_a_5703_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
if (lean_obj_tag(v___x_5716_) == 0)
{
lean_object* v_a_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; 
v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
lean_inc(v_a_5717_);
lean_dec_ref_known(v___x_5716_, 1);
v___x_5718_ = l_Lean_mkMVar(v_a_5703_);
v___x_5719_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5715_, v___x_5718_, v_a_5717_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
return v___x_5719_;
}
else
{
lean_dec(v_a_5715_);
lean_dec(v_a_5703_);
return v___x_5716_;
}
}
else
{
lean_object* v_a_5720_; lean_object* v___x_5722_; uint8_t v_isShared_5723_; uint8_t v_isSharedCheck_5727_; 
lean_dec(v_a_5703_);
v_a_5720_ = lean_ctor_get(v___x_5714_, 0);
v_isSharedCheck_5727_ = !lean_is_exclusive(v___x_5714_);
if (v_isSharedCheck_5727_ == 0)
{
v___x_5722_ = v___x_5714_;
v_isShared_5723_ = v_isSharedCheck_5727_;
goto v_resetjp_5721_;
}
else
{
lean_inc(v_a_5720_);
lean_dec(v___x_5714_);
v___x_5722_ = lean_box(0);
v_isShared_5723_ = v_isSharedCheck_5727_;
goto v_resetjp_5721_;
}
v_resetjp_5721_:
{
lean_object* v___x_5725_; 
if (v_isShared_5723_ == 0)
{
v___x_5725_ = v___x_5722_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_a_5720_);
v___x_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
return v___x_5725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object* v_snd_5728_, lean_object* v_a_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_){
_start:
{
lean_object* v_res_5740_; 
v_res_5740_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(v_snd_5728_, v_a_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_);
lean_dec(v___y_5738_);
lean_dec_ref(v___y_5737_);
lean_dec(v___y_5736_);
lean_dec_ref(v___y_5735_);
lean_dec(v___y_5734_);
lean_dec_ref(v___y_5733_);
lean_dec(v___y_5732_);
lean_dec_ref(v___y_5731_);
lean_dec(v___y_5730_);
lean_dec_ref(v_snd_5728_);
return v_res_5740_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5743_ = lean_box(0);
v___x_5744_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0));
v___x_5745_ = l_Lean_mkConst(v___x_5744_, v___x_5743_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(lean_object* v___x_5746_, lean_object* v_snd_5747_, lean_object* v___x_5748_, lean_object* v_i_5749_, lean_object* v_falseProof_5750_, lean_object* v_seq_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v___x_5762_; lean_object* v_congrThms_5763_; lean_object* v_simp_5764_; lean_object* v_symSimp_5765_; lean_object* v_symDSimp_5766_; lean_object* v_lastTag_5767_; lean_object* v_counters_5768_; lean_object* v_splitDiags_5769_; lean_object* v_ematchDiags_5770_; lean_object* v_lawfulEqCmpMap_5771_; lean_object* v_reflCmpMap_5772_; lean_object* v_anchors_5773_; lean_object* v_fvarAnchors_5774_; lean_object* v_instanceMap_5775_; lean_object* v_hoistedDecls_5776_; lean_object* v_proofInfos_5777_; lean_object* v_numBranches_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5831_; 
v___x_5762_ = lean_st_ref_take(v___y_5754_);
v_congrThms_5763_ = lean_ctor_get(v___x_5762_, 0);
v_simp_5764_ = lean_ctor_get(v___x_5762_, 1);
v_symSimp_5765_ = lean_ctor_get(v___x_5762_, 2);
v_symDSimp_5766_ = lean_ctor_get(v___x_5762_, 3);
v_lastTag_5767_ = lean_ctor_get(v___x_5762_, 4);
v_counters_5768_ = lean_ctor_get(v___x_5762_, 5);
v_splitDiags_5769_ = lean_ctor_get(v___x_5762_, 6);
v_ematchDiags_5770_ = lean_ctor_get(v___x_5762_, 7);
v_lawfulEqCmpMap_5771_ = lean_ctor_get(v___x_5762_, 8);
v_reflCmpMap_5772_ = lean_ctor_get(v___x_5762_, 9);
v_anchors_5773_ = lean_ctor_get(v___x_5762_, 10);
v_fvarAnchors_5774_ = lean_ctor_get(v___x_5762_, 11);
v_instanceMap_5775_ = lean_ctor_get(v___x_5762_, 12);
v_hoistedDecls_5776_ = lean_ctor_get(v___x_5762_, 13);
v_proofInfos_5777_ = lean_ctor_get(v___x_5762_, 14);
v_numBranches_5778_ = lean_ctor_get(v___x_5762_, 15);
v_isSharedCheck_5831_ = !lean_is_exclusive(v___x_5762_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5780_ = v___x_5762_;
v_isShared_5781_ = v_isSharedCheck_5831_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_numBranches_5778_);
lean_inc(v_proofInfos_5777_);
lean_inc(v_hoistedDecls_5776_);
lean_inc(v_instanceMap_5775_);
lean_inc(v_fvarAnchors_5774_);
lean_inc(v_anchors_5773_);
lean_inc(v_reflCmpMap_5772_);
lean_inc(v_lawfulEqCmpMap_5771_);
lean_inc(v_ematchDiags_5770_);
lean_inc(v_splitDiags_5769_);
lean_inc(v_counters_5768_);
lean_inc(v_lastTag_5767_);
lean_inc(v_symDSimp_5766_);
lean_inc(v_symSimp_5765_);
lean_inc(v_simp_5764_);
lean_inc(v_congrThms_5763_);
lean_dec(v___x_5762_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5831_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v___x_5782_ = lean_unsigned_to_nat(1u);
v___x_5783_ = lean_nat_sub(v___x_5746_, v___x_5782_);
v___x_5784_ = lean_nat_sub(v___x_5783_, v_i_5749_);
lean_dec(v___x_5783_);
v___x_5785_ = lean_nat_sub(v_numBranches_5778_, v___x_5784_);
lean_dec(v___x_5784_);
lean_dec(v_numBranches_5778_);
if (v_isShared_5781_ == 0)
{
lean_ctor_set(v___x_5780_, 15, v___x_5785_);
v___x_5787_ = v___x_5780_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_congrThms_5763_);
lean_ctor_set(v_reuseFailAlloc_5830_, 1, v_simp_5764_);
lean_ctor_set(v_reuseFailAlloc_5830_, 2, v_symSimp_5765_);
lean_ctor_set(v_reuseFailAlloc_5830_, 3, v_symDSimp_5766_);
lean_ctor_set(v_reuseFailAlloc_5830_, 4, v_lastTag_5767_);
lean_ctor_set(v_reuseFailAlloc_5830_, 5, v_counters_5768_);
lean_ctor_set(v_reuseFailAlloc_5830_, 6, v_splitDiags_5769_);
lean_ctor_set(v_reuseFailAlloc_5830_, 7, v_ematchDiags_5770_);
lean_ctor_set(v_reuseFailAlloc_5830_, 8, v_lawfulEqCmpMap_5771_);
lean_ctor_set(v_reuseFailAlloc_5830_, 9, v_reflCmpMap_5772_);
lean_ctor_set(v_reuseFailAlloc_5830_, 10, v_anchors_5773_);
lean_ctor_set(v_reuseFailAlloc_5830_, 11, v_fvarAnchors_5774_);
lean_ctor_set(v_reuseFailAlloc_5830_, 12, v_instanceMap_5775_);
lean_ctor_set(v_reuseFailAlloc_5830_, 13, v_hoistedDecls_5776_);
lean_ctor_set(v_reuseFailAlloc_5830_, 14, v_proofInfos_5777_);
lean_ctor_set(v_reuseFailAlloc_5830_, 15, v___x_5785_);
v___x_5787_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5788_; lean_object* v___x_5789_; 
v___x_5788_ = lean_st_ref_put(v___y_5754_, v___x_5787_);
v___x_5789_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5747_, v___y_5754_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v_mvarId_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
lean_inc(v_a_5790_);
lean_dec_ref_known(v___x_5789_, 1);
v_mvarId_5791_ = lean_ctor_get(v_snd_5747_, 1);
lean_inc(v_mvarId_5791_);
lean_dec_ref(v_snd_5747_);
v___x_5792_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_5793_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkHoistedDecls___boxed), 13, 3);
lean_closure_set(v___x_5793_, 0, v_a_5790_);
lean_closure_set(v___x_5793_, 1, v_falseProof_5750_);
lean_closure_set(v___x_5793_, 2, v___x_5792_);
v___x_5794_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5791_, v___x_5793_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_object* v_a_5795_; lean_object* v___x_5796_; 
v_a_5795_ = lean_ctor_get(v___x_5794_, 0);
lean_inc(v_a_5795_);
lean_dec_ref_known(v___x_5794_, 1);
v___x_5796_ = l_Lean_MVarId_assignFalseProof(v___x_5748_, v_a_5795_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5796_) == 0)
{
lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5804_; 
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5804_ == 0)
{
lean_object* v_unused_5805_; 
v_unused_5805_ = lean_ctor_get(v___x_5796_, 0);
lean_dec(v_unused_5805_);
v___x_5798_ = v___x_5796_;
v_isShared_5799_ = v_isSharedCheck_5804_;
goto v_resetjp_5797_;
}
else
{
lean_dec(v___x_5796_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5804_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v___x_5800_; lean_object* v___x_5802_; 
v___x_5800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5800_, 0, v_seq_5751_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_5800_);
v___x_5802_ = v___x_5798_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
else
{
lean_object* v_a_5806_; lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5813_; 
lean_dec(v_seq_5751_);
v_a_5806_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5813_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5813_ == 0)
{
v___x_5808_ = v___x_5796_;
v_isShared_5809_ = v_isSharedCheck_5813_;
goto v_resetjp_5807_;
}
else
{
lean_inc(v_a_5806_);
lean_dec(v___x_5796_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5813_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v___x_5811_; 
if (v_isShared_5809_ == 0)
{
v___x_5811_ = v___x_5808_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_a_5806_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
return v___x_5811_;
}
}
}
}
else
{
lean_object* v_a_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5821_; 
lean_dec(v_seq_5751_);
lean_dec(v___x_5748_);
v_a_5814_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5821_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5821_ == 0)
{
v___x_5816_ = v___x_5794_;
v_isShared_5817_ = v_isSharedCheck_5821_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_a_5814_);
lean_dec(v___x_5794_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5821_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v___x_5819_; 
if (v_isShared_5817_ == 0)
{
v___x_5819_ = v___x_5816_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_a_5814_);
v___x_5819_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
return v___x_5819_;
}
}
}
}
else
{
lean_object* v_a_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5829_; 
lean_dec(v_seq_5751_);
lean_dec_ref(v_falseProof_5750_);
lean_dec(v___x_5748_);
lean_dec_ref(v_snd_5747_);
v_a_5822_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5824_ = v___x_5789_;
v_isShared_5825_ = v_isSharedCheck_5829_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_a_5822_);
lean_dec(v___x_5789_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5829_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5827_; 
if (v_isShared_5825_ == 0)
{
v___x_5827_ = v___x_5824_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5822_);
v___x_5827_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
return v___x_5827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___boxed(lean_object* v___x_5832_, lean_object* v_snd_5833_, lean_object* v___x_5834_, lean_object* v_i_5835_, lean_object* v_falseProof_5836_, lean_object* v_seq_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5832_, v_snd_5833_, v___x_5834_, v_i_5835_, v_falseProof_5836_, v_seq_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
lean_dec(v___y_5846_);
lean_dec_ref(v___y_5845_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
lean_dec(v___y_5838_);
lean_dec(v_i_5835_);
lean_dec(v___x_5832_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v___x_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_){
_start:
{
if (lean_obj_tag(v_a_5850_) == 0)
{
lean_object* v___x_5852_; 
v___x_5852_ = l_List_reverse___redArg(v_a_5851_);
return v___x_5852_;
}
else
{
lean_object* v_head_5853_; lean_object* v_toGoalState_5854_; lean_object* v_tail_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5904_; 
v_head_5853_ = lean_ctor_get(v_a_5850_, 0);
lean_inc(v_head_5853_);
v_toGoalState_5854_ = lean_ctor_get(v_head_5853_, 0);
lean_inc_ref(v_toGoalState_5854_);
v_tail_5855_ = lean_ctor_get(v_a_5850_, 1);
v_isSharedCheck_5904_ = !lean_is_exclusive(v_a_5850_);
if (v_isSharedCheck_5904_ == 0)
{
lean_object* v_unused_5905_; 
v_unused_5905_ = lean_ctor_get(v_a_5850_, 0);
lean_dec(v_unused_5905_);
v___x_5857_ = v_a_5850_;
v_isShared_5858_ = v_isSharedCheck_5904_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_tail_5855_);
lean_dec(v_a_5850_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5904_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v_mvarId_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5902_; 
v_mvarId_5859_ = lean_ctor_get(v_head_5853_, 1);
v_isSharedCheck_5902_ = !lean_is_exclusive(v_head_5853_);
if (v_isSharedCheck_5902_ == 0)
{
lean_object* v_unused_5903_; 
v_unused_5903_ = lean_ctor_get(v_head_5853_, 0);
lean_dec(v_unused_5903_);
v___x_5861_ = v_head_5853_;
v_isShared_5862_ = v_isSharedCheck_5902_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_mvarId_5859_);
lean_dec(v_head_5853_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5902_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v_nextDeclIdx_5863_; lean_object* v_enodeMap_5864_; lean_object* v_exprs_5865_; lean_object* v_parents_5866_; lean_object* v_congrTable_5867_; lean_object* v_appMap_5868_; lean_object* v_indicesFound_5869_; lean_object* v_toProcess_5870_; lean_object* v_internalizing_5871_; uint8_t v_inconsistent_5872_; lean_object* v_nextIdx_5873_; lean_object* v_newRawFacts_5874_; lean_object* v_facts_5875_; lean_object* v_extThms_5876_; lean_object* v_ematch_5877_; lean_object* v_inj_5878_; lean_object* v_split_5879_; lean_object* v_clean_5880_; lean_object* v_sstates_5881_; lean_object* v_goalStack_5882_; uint64_t v_introBase_5883_; lean_object* v_numIntros_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5901_; 
v_nextDeclIdx_5863_ = lean_ctor_get(v_toGoalState_5854_, 0);
v_enodeMap_5864_ = lean_ctor_get(v_toGoalState_5854_, 1);
v_exprs_5865_ = lean_ctor_get(v_toGoalState_5854_, 2);
v_parents_5866_ = lean_ctor_get(v_toGoalState_5854_, 3);
v_congrTable_5867_ = lean_ctor_get(v_toGoalState_5854_, 4);
v_appMap_5868_ = lean_ctor_get(v_toGoalState_5854_, 5);
v_indicesFound_5869_ = lean_ctor_get(v_toGoalState_5854_, 6);
v_toProcess_5870_ = lean_ctor_get(v_toGoalState_5854_, 7);
v_internalizing_5871_ = lean_ctor_get(v_toGoalState_5854_, 8);
v_inconsistent_5872_ = lean_ctor_get_uint8(v_toGoalState_5854_, sizeof(void*)*20 + 8);
v_nextIdx_5873_ = lean_ctor_get(v_toGoalState_5854_, 9);
v_newRawFacts_5874_ = lean_ctor_get(v_toGoalState_5854_, 10);
v_facts_5875_ = lean_ctor_get(v_toGoalState_5854_, 11);
v_extThms_5876_ = lean_ctor_get(v_toGoalState_5854_, 12);
v_ematch_5877_ = lean_ctor_get(v_toGoalState_5854_, 13);
v_inj_5878_ = lean_ctor_get(v_toGoalState_5854_, 14);
v_split_5879_ = lean_ctor_get(v_toGoalState_5854_, 15);
v_clean_5880_ = lean_ctor_get(v_toGoalState_5854_, 16);
v_sstates_5881_ = lean_ctor_get(v_toGoalState_5854_, 17);
v_goalStack_5882_ = lean_ctor_get(v_toGoalState_5854_, 18);
v_introBase_5883_ = lean_ctor_get_uint64(v_toGoalState_5854_, sizeof(void*)*20);
v_numIntros_5884_ = lean_ctor_get(v_toGoalState_5854_, 19);
v_isSharedCheck_5901_ = !lean_is_exclusive(v_toGoalState_5854_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5886_ = v_toGoalState_5854_;
v_isShared_5887_ = v_isSharedCheck_5901_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_numIntros_5884_);
lean_inc(v_goalStack_5882_);
lean_inc(v_sstates_5881_);
lean_inc(v_clean_5880_);
lean_inc(v_split_5879_);
lean_inc(v_inj_5878_);
lean_inc(v_ematch_5877_);
lean_inc(v_extThms_5876_);
lean_inc(v_facts_5875_);
lean_inc(v_newRawFacts_5874_);
lean_inc(v_nextIdx_5873_);
lean_inc(v_internalizing_5871_);
lean_inc(v_toProcess_5870_);
lean_inc(v_indicesFound_5869_);
lean_inc(v_appMap_5868_);
lean_inc(v_congrTable_5867_);
lean_inc(v_parents_5866_);
lean_inc(v_exprs_5865_);
lean_inc(v_enodeMap_5864_);
lean_inc(v_nextDeclIdx_5863_);
lean_dec(v_toGoalState_5854_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5901_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5892_; 
v___x_5888_ = lean_unsigned_to_nat(0u);
v___x_5889_ = lean_array_get_size(v___x_5849_);
v___x_5890_ = l_Array_extract___redArg(v_goalStack_5882_, v___x_5888_, v___x_5889_);
lean_dec_ref(v_goalStack_5882_);
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 18, v___x_5890_);
v___x_5892_ = v___x_5886_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_nextDeclIdx_5863_);
lean_ctor_set(v_reuseFailAlloc_5900_, 1, v_enodeMap_5864_);
lean_ctor_set(v_reuseFailAlloc_5900_, 2, v_exprs_5865_);
lean_ctor_set(v_reuseFailAlloc_5900_, 3, v_parents_5866_);
lean_ctor_set(v_reuseFailAlloc_5900_, 4, v_congrTable_5867_);
lean_ctor_set(v_reuseFailAlloc_5900_, 5, v_appMap_5868_);
lean_ctor_set(v_reuseFailAlloc_5900_, 6, v_indicesFound_5869_);
lean_ctor_set(v_reuseFailAlloc_5900_, 7, v_toProcess_5870_);
lean_ctor_set(v_reuseFailAlloc_5900_, 8, v_internalizing_5871_);
lean_ctor_set(v_reuseFailAlloc_5900_, 9, v_nextIdx_5873_);
lean_ctor_set(v_reuseFailAlloc_5900_, 10, v_newRawFacts_5874_);
lean_ctor_set(v_reuseFailAlloc_5900_, 11, v_facts_5875_);
lean_ctor_set(v_reuseFailAlloc_5900_, 12, v_extThms_5876_);
lean_ctor_set(v_reuseFailAlloc_5900_, 13, v_ematch_5877_);
lean_ctor_set(v_reuseFailAlloc_5900_, 14, v_inj_5878_);
lean_ctor_set(v_reuseFailAlloc_5900_, 15, v_split_5879_);
lean_ctor_set(v_reuseFailAlloc_5900_, 16, v_clean_5880_);
lean_ctor_set(v_reuseFailAlloc_5900_, 17, v_sstates_5881_);
lean_ctor_set(v_reuseFailAlloc_5900_, 18, v___x_5890_);
lean_ctor_set(v_reuseFailAlloc_5900_, 19, v_numIntros_5884_);
lean_ctor_set_uint8(v_reuseFailAlloc_5900_, sizeof(void*)*20 + 8, v_inconsistent_5872_);
lean_ctor_set_uint64(v_reuseFailAlloc_5900_, sizeof(void*)*20, v_introBase_5883_);
v___x_5892_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
lean_object* v___x_5894_; 
if (v_isShared_5862_ == 0)
{
lean_ctor_set(v___x_5861_, 0, v___x_5892_);
v___x_5894_ = v___x_5861_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_mvarId_5859_);
v___x_5894_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
lean_object* v___x_5896_; 
if (v_isShared_5858_ == 0)
{
lean_ctor_set(v___x_5857_, 1, v_a_5851_);
lean_ctor_set(v___x_5857_, 0, v___x_5894_);
v___x_5896_ = v___x_5857_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v___x_5894_);
lean_ctor_set(v_reuseFailAlloc_5898_, 1, v_a_5851_);
v___x_5896_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
v_a_5850_ = v_tail_5855_;
v_a_5851_ = v___x_5896_;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v___x_5906_, lean_object* v_a_5907_, lean_object* v_a_5908_){
_start:
{
lean_object* v_res_5909_; 
v_res_5909_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5906_, v_a_5907_, v_a_5908_);
lean_dec_ref(v___x_5906_);
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(lean_object* v___x_5910_, lean_object* v_gs_5911_){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5912_ = lean_box(0);
v___x_5913_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5910_, v_gs_5911_, v___x_5912_);
return v___x_5913_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0___boxed(lean_object* v___x_5914_, lean_object* v_gs_5915_){
_start:
{
lean_object* v_res_5916_; 
v_res_5916_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5914_, v_gs_5915_);
lean_dec_ref(v___x_5914_);
return v_res_5916_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5917_, lean_object* v_a_5918_, lean_object* v_goal_5919_, lean_object* v___x_5920_, lean_object* v_snd_5921_, lean_object* v___x_5922_, uint8_t v_stopAtFirstFailure_5923_, lean_object* v___x_5924_, lean_object* v_as_x27_5925_, lean_object* v_b_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_){
_start:
{
if (lean_obj_tag(v_as_x27_5925_) == 0)
{
lean_object* v___x_5937_; 
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v___x_5937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5937_, 0, v_b_5926_);
return v___x_5937_;
}
else
{
lean_object* v_snd_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_6219_; 
v_snd_5938_ = lean_ctor_get(v_b_5926_, 1);
v_isSharedCheck_6219_ = !lean_is_exclusive(v_b_5926_);
if (v_isSharedCheck_6219_ == 0)
{
lean_object* v_unused_6220_; 
v_unused_6220_ = lean_ctor_get(v_b_5926_, 0);
lean_dec(v_unused_6220_);
v___x_5940_ = v_b_5926_;
v_isShared_5941_ = v_isSharedCheck_6219_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_snd_5938_);
lean_dec(v_b_5926_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_6219_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v_snd_5942_; lean_object* v_snd_5943_; lean_object* v_snd_5944_; lean_object* v_head_5945_; lean_object* v_tail_5946_; lean_object* v_fst_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_6217_; 
v_snd_5942_ = lean_ctor_get(v_snd_5938_, 1);
lean_inc(v_snd_5942_);
v_snd_5943_ = lean_ctor_get(v_snd_5942_, 1);
lean_inc(v_snd_5943_);
v_snd_5944_ = lean_ctor_get(v_snd_5943_, 1);
lean_inc(v_snd_5944_);
v_head_5945_ = lean_ctor_get(v_as_x27_5925_, 0);
v_tail_5946_ = lean_ctor_get(v_as_x27_5925_, 1);
v_fst_5947_ = lean_ctor_get(v_snd_5938_, 0);
v_isSharedCheck_6217_ = !lean_is_exclusive(v_snd_5938_);
if (v_isSharedCheck_6217_ == 0)
{
lean_object* v_unused_6218_; 
v_unused_6218_ = lean_ctor_get(v_snd_5938_, 1);
lean_dec(v_unused_6218_);
v___x_5949_ = v_snd_5938_;
v_isShared_5950_ = v_isSharedCheck_6217_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_fst_5947_);
lean_dec(v_snd_5938_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_6217_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v_fst_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_6215_; 
v_fst_5951_ = lean_ctor_get(v_snd_5942_, 0);
v_isSharedCheck_6215_ = !lean_is_exclusive(v_snd_5942_);
if (v_isSharedCheck_6215_ == 0)
{
lean_object* v_unused_6216_; 
v_unused_6216_ = lean_ctor_get(v_snd_5942_, 1);
lean_dec(v_unused_6216_);
v___x_5953_ = v_snd_5942_;
v_isShared_5954_ = v_isSharedCheck_6215_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_fst_5951_);
lean_dec(v_snd_5942_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_6215_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v_fst_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_6213_; 
v_fst_5955_ = lean_ctor_get(v_snd_5943_, 0);
v_isSharedCheck_6213_ = !lean_is_exclusive(v_snd_5943_);
if (v_isSharedCheck_6213_ == 0)
{
lean_object* v_unused_6214_; 
v_unused_6214_ = lean_ctor_get(v_snd_5943_, 1);
lean_dec(v_unused_6214_);
v___x_5957_ = v_snd_5943_;
v_isShared_5958_ = v_isSharedCheck_6213_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_fst_5955_);
lean_dec(v_snd_5943_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_6213_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v_start_5959_; lean_object* v_stop_5960_; lean_object* v_step_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; 
v_start_5959_ = lean_ctor_get(v_snd_5944_, 0);
v_stop_5960_ = lean_ctor_get(v_snd_5944_, 1);
v_step_5961_ = lean_ctor_get(v_snd_5944_, 2);
v___x_5962_ = lean_box(0);
v___x_5963_ = lean_nat_dec_lt(v_start_5959_, v_stop_5960_);
if (v___x_5963_ == 0)
{
lean_object* v___x_5965_; 
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
if (v_isShared_5958_ == 0)
{
v___x_5965_ = v___x_5957_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_snd_5944_);
v___x_5965_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
lean_object* v___x_5967_; 
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 1, v___x_5965_);
v___x_5967_ = v___x_5953_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_fst_5951_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5965_);
v___x_5967_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
lean_object* v___x_5969_; 
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_5967_);
v___x_5969_ = v___x_5949_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5974_; 
v_reuseFailAlloc_5974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5974_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_5974_, 1, v___x_5967_);
v___x_5969_ = v_reuseFailAlloc_5974_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___x_5971_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set(v___x_5940_, 1, v___x_5969_);
lean_ctor_set(v___x_5940_, 0, v___x_5962_);
v___x_5971_ = v___x_5940_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_5973_, 1, v___x_5969_);
v___x_5971_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
lean_object* v___x_5972_; 
v___x_5972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
return v___x_5972_;
}
}
}
}
}
else
{
lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_6209_; 
lean_inc(v_step_5961_);
lean_inc(v_stop_5960_);
lean_inc(v_start_5959_);
v_isSharedCheck_6209_ = !lean_is_exclusive(v_snd_5944_);
if (v_isSharedCheck_6209_ == 0)
{
lean_object* v_unused_6210_; lean_object* v_unused_6211_; lean_object* v_unused_6212_; 
v_unused_6210_ = lean_ctor_get(v_snd_5944_, 2);
lean_dec(v_unused_6210_);
v_unused_6211_ = lean_ctor_get(v_snd_5944_, 1);
lean_dec(v_unused_6211_);
v_unused_6212_ = lean_ctor_get(v_snd_5944_, 0);
lean_dec(v_unused_6212_);
v___x_5978_ = v_snd_5944_;
v_isShared_5979_ = v_isSharedCheck_6209_;
goto v_resetjp_5977_;
}
else
{
lean_dec(v_snd_5944_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_6209_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5980_ = lean_nat_add(v_start_5959_, v_step_5961_);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 0, v___x_5980_);
v___x_5982_ = v___x_5978_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_6208_, 1, v_stop_5960_);
lean_ctor_set(v_reuseFailAlloc_6208_, 2, v_step_5961_);
v___x_5982_ = v_reuseFailAlloc_6208_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5983_; 
lean_inc_ref(v_kp_5917_);
lean_inc(v___y_5935_);
lean_inc_ref(v___y_5934_);
lean_inc(v___y_5933_);
lean_inc_ref(v___y_5932_);
lean_inc(v___y_5931_);
lean_inc_ref(v___y_5930_);
lean_inc(v___y_5929_);
lean_inc_ref(v___y_5928_);
lean_inc(v___y_5927_);
lean_inc(v_head_5945_);
v___x_5983_ = lean_apply_11(v_kp_5917_, v_head_5945_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, lean_box(0));
if (lean_obj_tag(v___x_5983_) == 0)
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_6199_; 
v_a_5984_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_6199_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_5986_ = v___x_5983_;
v_isShared_5987_ = v_isSharedCheck_6199_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5983_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_6199_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
if (lean_obj_tag(v_a_5984_) == 0)
{
lean_object* v_seq_5988_; lean_object* v_ncb_x3f_5990_; lean_object* v_mvarId_6019_; lean_object* v___x_6020_; 
lean_del_object(v___x_5986_);
v_seq_5988_ = lean_ctor_get(v_a_5984_, 0);
lean_inc(v_seq_5988_);
lean_dec_ref_known(v_a_5984_, 1);
v_mvarId_6019_ = lean_ctor_get(v_head_5945_, 1);
lean_inc(v_mvarId_6019_);
v___x_6020_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_6019_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
if (lean_obj_tag(v___x_6020_) == 0)
{
lean_object* v_a_6021_; 
v_a_6021_ = lean_ctor_get(v___x_6020_, 0);
lean_inc(v_a_6021_);
lean_dec_ref_known(v___x_6020_, 1);
if (lean_obj_tag(v_a_6021_) == 1)
{
lean_object* v_val_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6077_; 
v_val_6022_ = lean_ctor_get(v_a_6021_, 0);
v_isSharedCheck_6077_ = !lean_is_exclusive(v_a_6021_);
if (v_isSharedCheck_6077_ == 0)
{
v___x_6024_ = v_a_6021_;
v_isShared_6025_ = v_isSharedCheck_6077_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_val_6022_);
lean_dec(v_a_6021_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6077_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6026_; 
lean_inc(v_seq_5988_);
lean_inc_ref(v_goal_5919_);
lean_inc(v_a_5918_);
v___x_6026_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_5918_, v_goal_5919_, v_seq_5988_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
if (lean_obj_tag(v___x_6026_) == 0)
{
lean_object* v_a_6027_; uint8_t v___x_6028_; 
v_a_6027_ = lean_ctor_get(v___x_6026_, 0);
lean_inc(v_a_6027_);
lean_dec_ref_known(v___x_6026_, 1);
v___x_6028_ = lean_unbox(v_a_6027_);
lean_dec(v_a_6027_);
if (v___x_6028_ == 0)
{
if (lean_obj_tag(v_fst_5955_) == 0)
{
lean_object* v___x_6029_; 
v___x_6029_ = l_Lean_Meta_Grind_saveState___redArg(v___y_5929_, v___y_5933_, v___y_5935_);
if (lean_obj_tag(v___x_6029_) == 0)
{
lean_object* v_a_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6035_; 
v_a_6030_ = lean_ctor_get(v___x_6029_, 0);
lean_inc(v_a_6030_);
lean_dec_ref_known(v___x_6029_, 1);
lean_inc(v_seq_5988_);
v___x_6031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6031_, 0, v_val_6022_);
lean_ctor_set(v___x_6031_, 1, v_seq_5988_);
v___x_6032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6032_, 0, v_start_5959_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
v___x_6033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6033_, 0, v_a_6030_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
if (v_isShared_6025_ == 0)
{
lean_ctor_set(v___x_6024_, 0, v___x_6033_);
v___x_6035_ = v___x_6024_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_6033_);
v___x_6035_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
v_ncb_x3f_5990_ = v___x_6035_;
goto v___jp_5989_;
}
}
else
{
lean_object* v_a_6037_; lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6044_; 
lean_del_object(v___x_6024_);
lean_dec(v_val_6022_);
lean_dec(v_seq_5988_);
lean_dec_ref(v___x_5982_);
lean_dec(v_start_5959_);
lean_del_object(v___x_5957_);
lean_del_object(v___x_5953_);
lean_dec(v_fst_5951_);
lean_del_object(v___x_5949_);
lean_dec(v_fst_5947_);
lean_del_object(v___x_5940_);
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v_a_6037_ = lean_ctor_get(v___x_6029_, 0);
v_isSharedCheck_6044_ = !lean_is_exclusive(v___x_6029_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_6039_ = v___x_6029_;
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
else
{
lean_inc(v_a_6037_);
lean_dec(v___x_6029_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
lean_object* v___x_6042_; 
if (v_isShared_6040_ == 0)
{
v___x_6042_ = v___x_6039_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
v___x_6042_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
return v___x_6042_;
}
}
}
}
else
{
lean_del_object(v___x_6024_);
lean_dec(v_val_6022_);
lean_dec(v_start_5959_);
v_ncb_x3f_5990_ = v_fst_5955_;
goto v___jp_5989_;
}
}
else
{
lean_object* v___x_6045_; 
lean_del_object(v___x_5957_);
lean_del_object(v___x_5953_);
lean_del_object(v___x_5949_);
lean_del_object(v___x_5940_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v___x_6045_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5920_, v_snd_5921_, v___x_5922_, v_start_5959_, v_val_6022_, v_seq_5988_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
lean_dec(v_start_5959_);
if (lean_obj_tag(v___x_6045_) == 0)
{
lean_object* v_a_6046_; lean_object* v___x_6048_; uint8_t v_isShared_6049_; uint8_t v_isSharedCheck_6060_; 
v_a_6046_ = lean_ctor_get(v___x_6045_, 0);
v_isSharedCheck_6060_ = !lean_is_exclusive(v___x_6045_);
if (v_isSharedCheck_6060_ == 0)
{
v___x_6048_ = v___x_6045_;
v_isShared_6049_ = v_isSharedCheck_6060_;
goto v_resetjp_6047_;
}
else
{
lean_inc(v_a_6046_);
lean_dec(v___x_6045_);
v___x_6048_ = lean_box(0);
v_isShared_6049_ = v_isSharedCheck_6060_;
goto v_resetjp_6047_;
}
v_resetjp_6047_:
{
lean_object* v___x_6051_; 
if (v_isShared_6025_ == 0)
{
lean_ctor_set(v___x_6024_, 0, v_a_6046_);
v___x_6051_ = v___x_6024_;
goto v_reusejp_6050_;
}
else
{
lean_object* v_reuseFailAlloc_6059_; 
v_reuseFailAlloc_6059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6046_);
v___x_6051_ = v_reuseFailAlloc_6059_;
goto v_reusejp_6050_;
}
v_reusejp_6050_:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6057_; 
v___x_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6052_, 0, v_fst_5955_);
lean_ctor_set(v___x_6052_, 1, v___x_5982_);
v___x_6053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6053_, 0, v_fst_5951_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6054_, 0, v_fst_5947_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6051_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
if (v_isShared_6049_ == 0)
{
lean_ctor_set(v___x_6048_, 0, v___x_6055_);
v___x_6057_ = v___x_6048_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v___x_6055_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
else
{
lean_object* v_a_6061_; lean_object* v___x_6063_; uint8_t v_isShared_6064_; uint8_t v_isSharedCheck_6068_; 
lean_del_object(v___x_6024_);
lean_dec_ref(v___x_5982_);
lean_dec(v_fst_5955_);
lean_dec(v_fst_5951_);
lean_dec(v_fst_5947_);
v_a_6061_ = lean_ctor_get(v___x_6045_, 0);
v_isSharedCheck_6068_ = !lean_is_exclusive(v___x_6045_);
if (v_isSharedCheck_6068_ == 0)
{
v___x_6063_ = v___x_6045_;
v_isShared_6064_ = v_isSharedCheck_6068_;
goto v_resetjp_6062_;
}
else
{
lean_inc(v_a_6061_);
lean_dec(v___x_6045_);
v___x_6063_ = lean_box(0);
v_isShared_6064_ = v_isSharedCheck_6068_;
goto v_resetjp_6062_;
}
v_resetjp_6062_:
{
lean_object* v___x_6066_; 
if (v_isShared_6064_ == 0)
{
v___x_6066_ = v___x_6063_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6067_; 
v_reuseFailAlloc_6067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6067_, 0, v_a_6061_);
v___x_6066_ = v_reuseFailAlloc_6067_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
return v___x_6066_;
}
}
}
}
}
else
{
lean_object* v_a_6069_; lean_object* v___x_6071_; uint8_t v_isShared_6072_; uint8_t v_isSharedCheck_6076_; 
lean_del_object(v___x_6024_);
lean_dec(v_val_6022_);
lean_dec(v_seq_5988_);
lean_dec_ref(v___x_5982_);
lean_dec(v_start_5959_);
lean_del_object(v___x_5957_);
lean_dec(v_fst_5955_);
lean_del_object(v___x_5953_);
lean_dec(v_fst_5951_);
lean_del_object(v___x_5949_);
lean_dec(v_fst_5947_);
lean_del_object(v___x_5940_);
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v_a_6069_ = lean_ctor_get(v___x_6026_, 0);
v_isSharedCheck_6076_ = !lean_is_exclusive(v___x_6026_);
if (v_isSharedCheck_6076_ == 0)
{
v___x_6071_ = v___x_6026_;
v_isShared_6072_ = v_isSharedCheck_6076_;
goto v_resetjp_6070_;
}
else
{
lean_inc(v_a_6069_);
lean_dec(v___x_6026_);
v___x_6071_ = lean_box(0);
v_isShared_6072_ = v_isSharedCheck_6076_;
goto v_resetjp_6070_;
}
v_resetjp_6070_:
{
lean_object* v___x_6074_; 
if (v_isShared_6072_ == 0)
{
v___x_6074_ = v___x_6071_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_a_6069_);
v___x_6074_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
return v___x_6074_;
}
}
}
}
}
else
{
uint8_t v___x_6078_; 
lean_dec(v_a_6021_);
lean_dec(v_start_5959_);
lean_del_object(v___x_5957_);
lean_del_object(v___x_5953_);
lean_del_object(v___x_5949_);
lean_del_object(v___x_5940_);
v___x_6078_ = l_List_isEmpty___redArg(v_seq_5988_);
if (v___x_6078_ == 0)
{
lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6079_ = lean_array_push(v_fst_5947_, v_seq_5988_);
v___x_6080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6080_, 0, v_fst_5955_);
lean_ctor_set(v___x_6080_, 1, v___x_5982_);
v___x_6081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6081_, 0, v_fst_5951_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6079_);
lean_ctor_set(v___x_6082_, 1, v___x_6081_);
v___x_6083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_5962_);
lean_ctor_set(v___x_6083_, 1, v___x_6082_);
v_as_x27_5925_ = v_tail_5946_;
v_b_5926_ = v___x_6083_;
goto _start;
}
else
{
lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; 
lean_dec(v_seq_5988_);
v___x_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6085_, 0, v_fst_5955_);
lean_ctor_set(v___x_6085_, 1, v___x_5982_);
v___x_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6086_, 0, v_fst_5951_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6087_, 0, v_fst_5947_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_5962_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v_as_x27_5925_ = v_tail_5946_;
v_b_5926_ = v___x_6088_;
goto _start;
}
}
}
else
{
lean_object* v_a_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6097_; 
lean_dec(v_seq_5988_);
lean_dec_ref(v___x_5982_);
lean_dec(v_start_5959_);
lean_del_object(v___x_5957_);
lean_dec(v_fst_5955_);
lean_del_object(v___x_5953_);
lean_dec(v_fst_5951_);
lean_del_object(v___x_5949_);
lean_dec(v_fst_5947_);
lean_del_object(v___x_5940_);
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v_a_6090_ = lean_ctor_get(v___x_6020_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v___x_6020_);
if (v_isSharedCheck_6097_ == 0)
{
v___x_6092_ = v___x_6020_;
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_a_6090_);
lean_dec(v___x_6020_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6095_; 
if (v_isShared_6093_ == 0)
{
v___x_6095_ = v___x_6092_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_a_6090_);
v___x_6095_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
return v___x_6095_;
}
}
}
v___jp_5989_:
{
uint8_t v___x_5991_; 
v___x_5991_ = l_List_isEmpty___redArg(v_seq_5988_);
if (v___x_5991_ == 0)
{
lean_object* v___x_5992_; lean_object* v___x_5994_; 
v___x_5992_ = lean_array_push(v_fst_5947_, v_seq_5988_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5982_);
lean_ctor_set(v___x_5957_, 0, v_ncb_x3f_5990_);
v___x_5994_ = v___x_5957_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v_ncb_x3f_5990_);
lean_ctor_set(v_reuseFailAlloc_6005_, 1, v___x_5982_);
v___x_5994_ = v_reuseFailAlloc_6005_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
lean_object* v___x_5996_; 
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 1, v___x_5994_);
v___x_5996_ = v___x_5953_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_fst_5951_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v___x_5994_);
v___x_5996_ = v_reuseFailAlloc_6004_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
lean_object* v___x_5998_; 
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_5996_);
lean_ctor_set(v___x_5949_, 0, v___x_5992_);
v___x_5998_ = v___x_5949_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v___x_5992_);
lean_ctor_set(v_reuseFailAlloc_6003_, 1, v___x_5996_);
v___x_5998_ = v_reuseFailAlloc_6003_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
lean_object* v___x_6000_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set(v___x_5940_, 1, v___x_5998_);
lean_ctor_set(v___x_5940_, 0, v___x_5962_);
v___x_6000_ = v___x_5940_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_6002_, 1, v___x_5998_);
v___x_6000_ = v_reuseFailAlloc_6002_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
v_as_x27_5925_ = v_tail_5946_;
v_b_5926_ = v___x_6000_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_6007_; 
lean_dec(v_seq_5988_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5982_);
lean_ctor_set(v___x_5957_, 0, v_ncb_x3f_5990_);
v___x_6007_ = v___x_5957_;
goto v_reusejp_6006_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_ncb_x3f_5990_);
lean_ctor_set(v_reuseFailAlloc_6018_, 1, v___x_5982_);
v___x_6007_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6006_;
}
v_reusejp_6006_:
{
lean_object* v___x_6009_; 
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 1, v___x_6007_);
v___x_6009_ = v___x_5953_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6017_; 
v_reuseFailAlloc_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6017_, 0, v_fst_5951_);
lean_ctor_set(v_reuseFailAlloc_6017_, 1, v___x_6007_);
v___x_6009_ = v_reuseFailAlloc_6017_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
lean_object* v___x_6011_; 
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_6009_);
v___x_6011_ = v___x_5949_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_6016_, 1, v___x_6009_);
v___x_6011_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
lean_object* v___x_6013_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set(v___x_5940_, 1, v___x_6011_);
lean_ctor_set(v___x_5940_, 0, v___x_5962_);
v___x_6013_ = v___x_5940_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_6015_, 1, v___x_6011_);
v___x_6013_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
v_as_x27_5925_ = v_tail_5946_;
v_b_5926_ = v___x_6013_;
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
lean_dec(v_start_5959_);
if (lean_obj_tag(v_fst_5955_) == 1)
{
lean_object* v_val_6098_; lean_object* v_snd_6099_; lean_object* v_snd_6100_; lean_object* v_fst_6101_; lean_object* v___x_6103_; uint8_t v_isShared_6104_; uint8_t v_isSharedCheck_6156_; 
lean_dec_ref_known(v_a_5984_, 1);
lean_del_object(v___x_5986_);
lean_del_object(v___x_5953_);
lean_del_object(v___x_5949_);
lean_del_object(v___x_5940_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v_val_6098_ = lean_ctor_get(v_fst_5955_, 0);
lean_inc(v_val_6098_);
v_snd_6099_ = lean_ctor_get(v_val_6098_, 1);
lean_inc(v_snd_6099_);
v_snd_6100_ = lean_ctor_get(v_snd_6099_, 1);
lean_inc(v_snd_6100_);
v_fst_6101_ = lean_ctor_get(v_val_6098_, 0);
v_isSharedCheck_6156_ = !lean_is_exclusive(v_val_6098_);
if (v_isSharedCheck_6156_ == 0)
{
lean_object* v_unused_6157_; 
v_unused_6157_ = lean_ctor_get(v_val_6098_, 1);
lean_dec(v_unused_6157_);
v___x_6103_ = v_val_6098_;
v_isShared_6104_ = v_isSharedCheck_6156_;
goto v_resetjp_6102_;
}
else
{
lean_inc(v_fst_6101_);
lean_dec(v_val_6098_);
v___x_6103_ = lean_box(0);
v_isShared_6104_ = v_isSharedCheck_6156_;
goto v_resetjp_6102_;
}
v_resetjp_6102_:
{
lean_object* v_fst_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6154_; 
v_fst_6105_ = lean_ctor_get(v_snd_6099_, 0);
v_isSharedCheck_6154_ = !lean_is_exclusive(v_snd_6099_);
if (v_isSharedCheck_6154_ == 0)
{
lean_object* v_unused_6155_; 
v_unused_6155_ = lean_ctor_get(v_snd_6099_, 1);
lean_dec(v_unused_6155_);
v___x_6107_ = v_snd_6099_;
v_isShared_6108_ = v_isSharedCheck_6154_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_fst_6105_);
lean_dec(v_snd_6099_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6154_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v_fst_6109_; lean_object* v_snd_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6153_; 
v_fst_6109_ = lean_ctor_get(v_snd_6100_, 0);
v_snd_6110_ = lean_ctor_get(v_snd_6100_, 1);
v_isSharedCheck_6153_ = !lean_is_exclusive(v_snd_6100_);
if (v_isSharedCheck_6153_ == 0)
{
v___x_6112_ = v_snd_6100_;
v_isShared_6113_ = v_isSharedCheck_6153_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_snd_6110_);
lean_inc(v_fst_6109_);
lean_dec(v_snd_6100_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6153_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6114_; 
v___x_6114_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_fst_6101_, v___y_5929_, v___y_5933_, v___y_5935_);
if (lean_obj_tag(v___x_6114_) == 0)
{
lean_object* v___x_6115_; 
lean_dec_ref_known(v___x_6114_, 1);
v___x_6115_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5920_, v_snd_5921_, v___x_5922_, v_fst_6105_, v_fst_6109_, v_snd_6110_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
lean_dec(v_fst_6105_);
if (lean_obj_tag(v___x_6115_) == 0)
{
lean_object* v_a_6116_; lean_object* v___x_6118_; uint8_t v_isShared_6119_; uint8_t v_isSharedCheck_6136_; 
v_a_6116_ = lean_ctor_get(v___x_6115_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v___x_6115_);
if (v_isSharedCheck_6136_ == 0)
{
v___x_6118_ = v___x_6115_;
v_isShared_6119_ = v_isSharedCheck_6136_;
goto v_resetjp_6117_;
}
else
{
lean_inc(v_a_6116_);
lean_dec(v___x_6115_);
v___x_6118_ = lean_box(0);
v_isShared_6119_ = v_isSharedCheck_6136_;
goto v_resetjp_6117_;
}
v_resetjp_6117_:
{
lean_object* v___x_6120_; lean_object* v___x_6122_; 
v___x_6120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6120_, 0, v_a_6116_);
if (v_isShared_6113_ == 0)
{
lean_ctor_set(v___x_6112_, 1, v___x_5982_);
lean_ctor_set(v___x_6112_, 0, v_fst_5955_);
v___x_6122_ = v___x_6112_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_6135_, 1, v___x_5982_);
v___x_6122_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
lean_object* v___x_6124_; 
if (v_isShared_6108_ == 0)
{
lean_ctor_set(v___x_6107_, 1, v___x_6122_);
lean_ctor_set(v___x_6107_, 0, v_fst_5951_);
v___x_6124_ = v___x_6107_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_fst_5951_);
lean_ctor_set(v_reuseFailAlloc_6134_, 1, v___x_6122_);
v___x_6124_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
lean_object* v___x_6126_; 
if (v_isShared_6104_ == 0)
{
lean_ctor_set(v___x_6103_, 1, v___x_6124_);
lean_ctor_set(v___x_6103_, 0, v_fst_5947_);
v___x_6126_ = v___x_6103_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_6133_, 1, v___x_6124_);
v___x_6126_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
lean_object* v___x_6128_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_6126_);
lean_ctor_set(v___x_5957_, 0, v___x_6120_);
v___x_6128_ = v___x_5957_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v___x_6120_);
lean_ctor_set(v_reuseFailAlloc_6132_, 1, v___x_6126_);
v___x_6128_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
lean_object* v___x_6130_; 
if (v_isShared_6119_ == 0)
{
lean_ctor_set(v___x_6118_, 0, v___x_6128_);
v___x_6130_ = v___x_6118_;
goto v_reusejp_6129_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v___x_6128_);
v___x_6130_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6129_;
}
v_reusejp_6129_:
{
return v___x_6130_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6144_; 
lean_del_object(v___x_6112_);
lean_del_object(v___x_6107_);
lean_del_object(v___x_6103_);
lean_dec_ref_known(v_fst_5955_, 1);
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5957_);
lean_dec(v_fst_5951_);
lean_dec(v_fst_5947_);
v_a_6137_ = lean_ctor_get(v___x_6115_, 0);
v_isSharedCheck_6144_ = !lean_is_exclusive(v___x_6115_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6139_ = v___x_6115_;
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v___x_6115_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6142_; 
if (v_isShared_6140_ == 0)
{
v___x_6142_ = v___x_6139_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_a_6137_);
v___x_6142_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
return v___x_6142_;
}
}
}
}
else
{
lean_object* v_a_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6152_; 
lean_del_object(v___x_6112_);
lean_dec(v_snd_6110_);
lean_dec(v_fst_6109_);
lean_del_object(v___x_6107_);
lean_dec(v_fst_6105_);
lean_del_object(v___x_6103_);
lean_dec_ref_known(v_fst_5955_, 1);
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5957_);
lean_dec(v_fst_5951_);
lean_dec(v_fst_5947_);
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
v_a_6145_ = lean_ctor_get(v___x_6114_, 0);
v_isSharedCheck_6152_ = !lean_is_exclusive(v___x_6114_);
if (v_isSharedCheck_6152_ == 0)
{
v___x_6147_ = v___x_6114_;
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_a_6145_);
lean_dec(v___x_6114_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6150_; 
if (v_isShared_6148_ == 0)
{
v___x_6150_ = v___x_6147_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_a_6145_);
v___x_6150_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
return v___x_6150_;
}
}
}
}
}
}
}
else
{
if (v_stopAtFirstFailure_5923_ == 0)
{
lean_object* v_gs_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6162_; 
lean_del_object(v___x_5986_);
v_gs_6158_ = lean_ctor_get(v_a_5984_, 0);
lean_inc(v_gs_6158_);
lean_dec_ref_known(v_a_5984_, 1);
v___x_6159_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5924_, v_gs_6158_);
v___x_6160_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_5951_, v___x_6159_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5982_);
v___x_6162_ = v___x_5957_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6173_; 
v_reuseFailAlloc_6173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6173_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_6173_, 1, v___x_5982_);
v___x_6162_ = v_reuseFailAlloc_6173_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
lean_object* v___x_6164_; 
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 1, v___x_6162_);
lean_ctor_set(v___x_5953_, 0, v___x_6160_);
v___x_6164_ = v___x_5953_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6160_);
lean_ctor_set(v_reuseFailAlloc_6172_, 1, v___x_6162_);
v___x_6164_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
lean_object* v___x_6166_; 
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_6164_);
v___x_6166_ = v___x_5949_;
goto v_reusejp_6165_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_6171_, 1, v___x_6164_);
v___x_6166_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6165_;
}
v_reusejp_6165_:
{
lean_object* v___x_6168_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set(v___x_5940_, 1, v___x_6166_);
lean_ctor_set(v___x_5940_, 0, v___x_5962_);
v___x_6168_ = v___x_5940_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_6170_, 1, v___x_6166_);
v___x_6168_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
v_as_x27_5925_ = v_tail_5946_;
v_b_5926_ = v___x_6168_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_gs_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6198_; 
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v_gs_6174_ = lean_ctor_get(v_a_5984_, 0);
v_isSharedCheck_6198_ = !lean_is_exclusive(v_a_5984_);
if (v_isSharedCheck_6198_ == 0)
{
v___x_6176_ = v_a_5984_;
v_isShared_6177_ = v_isSharedCheck_6198_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_gs_6174_);
lean_dec(v_a_5984_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6198_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v___x_6178_; lean_object* v___x_6180_; 
v___x_6178_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5924_, v_gs_6174_);
if (v_isShared_6177_ == 0)
{
lean_ctor_set(v___x_6176_, 0, v___x_6178_);
v___x_6180_ = v___x_6176_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6197_; 
v_reuseFailAlloc_6197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6197_, 0, v___x_6178_);
v___x_6180_ = v_reuseFailAlloc_6197_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
lean_object* v___x_6181_; lean_object* v___x_6183_; 
v___x_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5982_);
v___x_6183_ = v___x_5957_;
goto v_reusejp_6182_;
}
else
{
lean_object* v_reuseFailAlloc_6196_; 
v_reuseFailAlloc_6196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_6196_, 1, v___x_5982_);
v___x_6183_ = v_reuseFailAlloc_6196_;
goto v_reusejp_6182_;
}
v_reusejp_6182_:
{
lean_object* v___x_6185_; 
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 1, v___x_6183_);
v___x_6185_ = v___x_5953_;
goto v_reusejp_6184_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_fst_5951_);
lean_ctor_set(v_reuseFailAlloc_6195_, 1, v___x_6183_);
v___x_6185_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6184_;
}
v_reusejp_6184_:
{
lean_object* v___x_6187_; 
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_6185_);
v___x_6187_ = v___x_5949_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_6194_, 1, v___x_6185_);
v___x_6187_ = v_reuseFailAlloc_6194_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
lean_object* v___x_6189_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set(v___x_5940_, 1, v___x_6187_);
lean_ctor_set(v___x_5940_, 0, v___x_6181_);
v___x_6189_ = v___x_5940_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6181_);
lean_ctor_set(v_reuseFailAlloc_6193_, 1, v___x_6187_);
v___x_6189_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
lean_object* v___x_6191_; 
if (v_isShared_5987_ == 0)
{
lean_ctor_set(v___x_5986_, 0, v___x_6189_);
v___x_6191_ = v___x_5986_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6189_);
v___x_6191_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
return v___x_6191_;
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
lean_object* v_a_6200_; lean_object* v___x_6202_; uint8_t v_isShared_6203_; uint8_t v_isSharedCheck_6207_; 
lean_dec_ref(v___x_5982_);
lean_dec(v_start_5959_);
lean_del_object(v___x_5957_);
lean_dec(v_fst_5955_);
lean_del_object(v___x_5953_);
lean_dec(v_fst_5951_);
lean_del_object(v___x_5949_);
lean_dec(v_fst_5947_);
lean_del_object(v___x_5940_);
lean_dec(v___x_5922_);
lean_dec_ref(v_snd_5921_);
lean_dec_ref(v_goal_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_kp_5917_);
v_a_6200_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_6207_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_6207_ == 0)
{
v___x_6202_ = v___x_5983_;
v_isShared_6203_ = v_isSharedCheck_6207_;
goto v_resetjp_6201_;
}
else
{
lean_inc(v_a_6200_);
lean_dec(v___x_5983_);
v___x_6202_ = lean_box(0);
v_isShared_6203_ = v_isSharedCheck_6207_;
goto v_resetjp_6201_;
}
v_resetjp_6201_:
{
lean_object* v___x_6205_; 
if (v_isShared_6203_ == 0)
{
v___x_6205_ = v___x_6202_;
goto v_reusejp_6204_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v_a_6200_);
v___x_6205_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6204_;
}
v_reusejp_6204_:
{
return v___x_6205_;
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
lean_object* v_kp_6221_ = _args[0];
lean_object* v_a_6222_ = _args[1];
lean_object* v_goal_6223_ = _args[2];
lean_object* v___x_6224_ = _args[3];
lean_object* v_snd_6225_ = _args[4];
lean_object* v___x_6226_ = _args[5];
lean_object* v_stopAtFirstFailure_6227_ = _args[6];
lean_object* v___x_6228_ = _args[7];
lean_object* v_as_x27_6229_ = _args[8];
lean_object* v_b_6230_ = _args[9];
lean_object* v___y_6231_ = _args[10];
lean_object* v___y_6232_ = _args[11];
lean_object* v___y_6233_ = _args[12];
lean_object* v___y_6234_ = _args[13];
lean_object* v___y_6235_ = _args[14];
lean_object* v___y_6236_ = _args[15];
lean_object* v___y_6237_ = _args[16];
lean_object* v___y_6238_ = _args[17];
lean_object* v___y_6239_ = _args[18];
lean_object* v___y_6240_ = _args[19];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6241_; lean_object* v_res_6242_; 
v_stopAtFirstFailure_boxed_6241_ = lean_unbox(v_stopAtFirstFailure_6227_);
v_res_6242_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6221_, v_a_6222_, v_goal_6223_, v___x_6224_, v_snd_6225_, v___x_6226_, v_stopAtFirstFailure_boxed_6241_, v___x_6228_, v_as_x27_6229_, v_b_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_);
lean_dec(v___y_6239_);
lean_dec_ref(v___y_6238_);
lean_dec(v___y_6237_);
lean_dec_ref(v___y_6236_);
lean_dec(v___y_6235_);
lean_dec_ref(v___y_6234_);
lean_dec(v___y_6233_);
lean_dec_ref(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec(v_as_x27_6229_);
lean_dec_ref(v___x_6228_);
lean_dec(v___x_6224_);
return v_res_6242_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v___x_6243_, lean_object* v_c_6244_, lean_object* v___x_6245_, lean_object* v___x_6246_, lean_object* v___x_6247_, uint64_t v_a_6248_, lean_object* v_a_6249_, lean_object* v_a_6250_){
_start:
{
if (lean_obj_tag(v_a_6249_) == 0)
{
lean_object* v___x_6251_; 
lean_dec_ref(v___x_6247_);
lean_dec(v___x_6246_);
lean_dec_ref(v___x_6245_);
lean_dec_ref(v___x_6243_);
v___x_6251_ = lean_array_to_list(v_a_6250_);
return v___x_6251_;
}
else
{
lean_object* v_split_6252_; lean_object* v_head_6253_; lean_object* v_tail_6254_; lean_object* v___x_6256_; uint8_t v_isShared_6257_; uint8_t v_isSharedCheck_6305_; 
v_split_6252_ = lean_ctor_get(v___x_6243_, 15);
lean_inc_ref(v_split_6252_);
v_head_6253_ = lean_ctor_get(v_a_6249_, 0);
v_tail_6254_ = lean_ctor_get(v_a_6249_, 1);
v_isSharedCheck_6305_ = !lean_is_exclusive(v_a_6249_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6256_ = v_a_6249_;
v_isShared_6257_ = v_isSharedCheck_6305_;
goto v_resetjp_6255_;
}
else
{
lean_inc(v_tail_6254_);
lean_inc(v_head_6253_);
lean_dec(v_a_6249_);
v___x_6256_ = lean_box(0);
v_isShared_6257_ = v_isSharedCheck_6305_;
goto v_resetjp_6255_;
}
v_resetjp_6255_:
{
lean_object* v_nextDeclIdx_6258_; lean_object* v_enodeMap_6259_; lean_object* v_exprs_6260_; lean_object* v_parents_6261_; lean_object* v_congrTable_6262_; lean_object* v_appMap_6263_; lean_object* v_indicesFound_6264_; lean_object* v_toProcess_6265_; lean_object* v_internalizing_6266_; uint8_t v_inconsistent_6267_; lean_object* v_nextIdx_6268_; lean_object* v_newRawFacts_6269_; lean_object* v_facts_6270_; lean_object* v_extThms_6271_; lean_object* v_ematch_6272_; lean_object* v_inj_6273_; lean_object* v_clean_6274_; lean_object* v_sstates_6275_; uint64_t v_introBase_6276_; lean_object* v_numIntros_6277_; lean_object* v_candidates_6278_; lean_object* v_added_6279_; lean_object* v_resolved_6280_; lean_object* v_trace_6281_; lean_object* v_lookaheads_6282_; lean_object* v_argPosMap_6283_; lean_object* v_argsAt_6284_; lean_object* v___x_6286_; uint8_t v_isShared_6287_; uint8_t v_isSharedCheck_6304_; 
v_nextDeclIdx_6258_ = lean_ctor_get(v___x_6243_, 0);
v_enodeMap_6259_ = lean_ctor_get(v___x_6243_, 1);
v_exprs_6260_ = lean_ctor_get(v___x_6243_, 2);
v_parents_6261_ = lean_ctor_get(v___x_6243_, 3);
v_congrTable_6262_ = lean_ctor_get(v___x_6243_, 4);
v_appMap_6263_ = lean_ctor_get(v___x_6243_, 5);
v_indicesFound_6264_ = lean_ctor_get(v___x_6243_, 6);
v_toProcess_6265_ = lean_ctor_get(v___x_6243_, 7);
v_internalizing_6266_ = lean_ctor_get(v___x_6243_, 8);
v_inconsistent_6267_ = lean_ctor_get_uint8(v___x_6243_, sizeof(void*)*20 + 8);
v_nextIdx_6268_ = lean_ctor_get(v___x_6243_, 9);
v_newRawFacts_6269_ = lean_ctor_get(v___x_6243_, 10);
v_facts_6270_ = lean_ctor_get(v___x_6243_, 11);
v_extThms_6271_ = lean_ctor_get(v___x_6243_, 12);
v_ematch_6272_ = lean_ctor_get(v___x_6243_, 13);
v_inj_6273_ = lean_ctor_get(v___x_6243_, 14);
v_clean_6274_ = lean_ctor_get(v___x_6243_, 16);
v_sstates_6275_ = lean_ctor_get(v___x_6243_, 17);
v_introBase_6276_ = lean_ctor_get_uint64(v___x_6243_, sizeof(void*)*20);
v_numIntros_6277_ = lean_ctor_get(v___x_6243_, 19);
v_candidates_6278_ = lean_ctor_get(v_split_6252_, 0);
v_added_6279_ = lean_ctor_get(v_split_6252_, 1);
v_resolved_6280_ = lean_ctor_get(v_split_6252_, 2);
v_trace_6281_ = lean_ctor_get(v_split_6252_, 3);
v_lookaheads_6282_ = lean_ctor_get(v_split_6252_, 4);
v_argPosMap_6283_ = lean_ctor_get(v_split_6252_, 5);
v_argsAt_6284_ = lean_ctor_get(v_split_6252_, 6);
v_isSharedCheck_6304_ = !lean_is_exclusive(v_split_6252_);
if (v_isSharedCheck_6304_ == 0)
{
v___x_6286_ = v_split_6252_;
v_isShared_6287_ = v_isSharedCheck_6304_;
goto v_resetjp_6285_;
}
else
{
lean_inc(v_argsAt_6284_);
lean_inc(v_argPosMap_6283_);
lean_inc(v_lookaheads_6282_);
lean_inc(v_trace_6281_);
lean_inc(v_resolved_6280_);
lean_inc(v_added_6279_);
lean_inc(v_candidates_6278_);
lean_dec(v_split_6252_);
v___x_6286_ = lean_box(0);
v_isShared_6287_ = v_isSharedCheck_6304_;
goto v_resetjp_6285_;
}
v_resetjp_6285_:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6292_; 
v___x_6288_ = lean_array_get_size(v_a_6250_);
v___x_6289_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_6244_);
lean_inc(v___x_6246_);
lean_inc_ref(v___x_6245_);
v___x_6290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6290_, 0, v___x_6245_);
lean_ctor_set(v___x_6290_, 1, v___x_6288_);
lean_ctor_set(v___x_6290_, 2, v___x_6246_);
lean_ctor_set(v___x_6290_, 3, v___x_6289_);
if (v_isShared_6257_ == 0)
{
lean_ctor_set(v___x_6256_, 1, v_trace_6281_);
lean_ctor_set(v___x_6256_, 0, v___x_6290_);
v___x_6292_ = v___x_6256_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6303_; 
v_reuseFailAlloc_6303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6303_, 0, v___x_6290_);
lean_ctor_set(v_reuseFailAlloc_6303_, 1, v_trace_6281_);
v___x_6292_ = v_reuseFailAlloc_6303_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
lean_object* v___x_6294_; 
if (v_isShared_6287_ == 0)
{
lean_ctor_set(v___x_6286_, 3, v___x_6292_);
v___x_6294_ = v___x_6286_;
goto v_reusejp_6293_;
}
else
{
lean_object* v_reuseFailAlloc_6302_; 
v_reuseFailAlloc_6302_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_6302_, 0, v_candidates_6278_);
lean_ctor_set(v_reuseFailAlloc_6302_, 1, v_added_6279_);
lean_ctor_set(v_reuseFailAlloc_6302_, 2, v_resolved_6280_);
lean_ctor_set(v_reuseFailAlloc_6302_, 3, v___x_6292_);
lean_ctor_set(v_reuseFailAlloc_6302_, 4, v_lookaheads_6282_);
lean_ctor_set(v_reuseFailAlloc_6302_, 5, v_argPosMap_6283_);
lean_ctor_set(v_reuseFailAlloc_6302_, 6, v_argsAt_6284_);
v___x_6294_ = v_reuseFailAlloc_6302_;
goto v_reusejp_6293_;
}
v_reusejp_6293_:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; uint64_t v___x_6297_; uint64_t v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; 
lean_inc(v_numIntros_6277_);
lean_inc_ref(v___x_6247_);
lean_inc_ref(v_sstates_6275_);
lean_inc_ref(v_clean_6274_);
lean_inc_ref(v_inj_6273_);
lean_inc_ref(v_ematch_6272_);
lean_inc_ref(v_extThms_6271_);
lean_inc_ref(v_facts_6270_);
lean_inc_ref(v_newRawFacts_6269_);
lean_inc(v_nextIdx_6268_);
lean_inc_ref(v_internalizing_6266_);
lean_inc_ref(v_toProcess_6265_);
lean_inc_ref(v_indicesFound_6264_);
lean_inc_ref(v_appMap_6263_);
lean_inc_ref(v_congrTable_6262_);
lean_inc_ref(v_parents_6261_);
lean_inc_ref(v_exprs_6260_);
lean_inc_ref(v_enodeMap_6259_);
lean_inc(v_nextDeclIdx_6258_);
v___x_6295_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v___x_6295_, 0, v_nextDeclIdx_6258_);
lean_ctor_set(v___x_6295_, 1, v_enodeMap_6259_);
lean_ctor_set(v___x_6295_, 2, v_exprs_6260_);
lean_ctor_set(v___x_6295_, 3, v_parents_6261_);
lean_ctor_set(v___x_6295_, 4, v_congrTable_6262_);
lean_ctor_set(v___x_6295_, 5, v_appMap_6263_);
lean_ctor_set(v___x_6295_, 6, v_indicesFound_6264_);
lean_ctor_set(v___x_6295_, 7, v_toProcess_6265_);
lean_ctor_set(v___x_6295_, 8, v_internalizing_6266_);
lean_ctor_set(v___x_6295_, 9, v_nextIdx_6268_);
lean_ctor_set(v___x_6295_, 10, v_newRawFacts_6269_);
lean_ctor_set(v___x_6295_, 11, v_facts_6270_);
lean_ctor_set(v___x_6295_, 12, v_extThms_6271_);
lean_ctor_set(v___x_6295_, 13, v_ematch_6272_);
lean_ctor_set(v___x_6295_, 14, v_inj_6273_);
lean_ctor_set(v___x_6295_, 15, v___x_6294_);
lean_ctor_set(v___x_6295_, 16, v_clean_6274_);
lean_ctor_set(v___x_6295_, 17, v_sstates_6275_);
lean_ctor_set(v___x_6295_, 18, v___x_6247_);
lean_ctor_set(v___x_6295_, 19, v_numIntros_6277_);
lean_ctor_set_uint8(v___x_6295_, sizeof(void*)*20 + 8, v_inconsistent_6267_);
lean_ctor_set_uint64(v___x_6295_, sizeof(void*)*20, v_introBase_6276_);
v___x_6296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6296_, 0, v___x_6295_);
lean_ctor_set(v___x_6296_, 1, v_head_6253_);
v___x_6297_ = lean_uint64_of_nat(v___x_6288_);
v___x_6298_ = lean_uint64_mix_hash(v_a_6248_, v___x_6297_);
v___x_6299_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_6296_, v___x_6298_);
v___x_6300_ = lean_array_push(v_a_6250_, v___x_6299_);
v_a_6249_ = v_tail_6254_;
v_a_6250_ = v___x_6300_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v___x_6306_, lean_object* v_c_6307_, lean_object* v___x_6308_, lean_object* v___x_6309_, lean_object* v___x_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_){
_start:
{
uint64_t v_a_118053__boxed_6314_; lean_object* v_res_6315_; 
v_a_118053__boxed_6314_ = lean_unbox_uint64(v_a_6311_);
lean_dec_ref(v_a_6311_);
v_res_6315_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_6306_, v_c_6307_, v___x_6308_, v___x_6309_, v___x_6310_, v_a_118053__boxed_6314_, v_a_6312_, v_a_6313_);
lean_dec_ref(v_c_6307_);
return v_res_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_6316_, lean_object* v_x_6317_, lean_object* v_x_6318_, lean_object* v_x_6319_){
_start:
{
lean_object* v_ks_6320_; lean_object* v_vs_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6345_; 
v_ks_6320_ = lean_ctor_get(v_x_6316_, 0);
v_vs_6321_ = lean_ctor_get(v_x_6316_, 1);
v_isSharedCheck_6345_ = !lean_is_exclusive(v_x_6316_);
if (v_isSharedCheck_6345_ == 0)
{
v___x_6323_ = v_x_6316_;
v_isShared_6324_ = v_isSharedCheck_6345_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_vs_6321_);
lean_inc(v_ks_6320_);
lean_dec(v_x_6316_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6345_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v___x_6325_; uint8_t v___x_6326_; 
v___x_6325_ = lean_array_get_size(v_ks_6320_);
v___x_6326_ = lean_nat_dec_lt(v_x_6317_, v___x_6325_);
if (v___x_6326_ == 0)
{
lean_object* v___x_6327_; lean_object* v___x_6328_; lean_object* v___x_6330_; 
lean_dec(v_x_6317_);
v___x_6327_ = lean_array_push(v_ks_6320_, v_x_6318_);
v___x_6328_ = lean_array_push(v_vs_6321_, v_x_6319_);
if (v_isShared_6324_ == 0)
{
lean_ctor_set(v___x_6323_, 1, v___x_6328_);
lean_ctor_set(v___x_6323_, 0, v___x_6327_);
v___x_6330_ = v___x_6323_;
goto v_reusejp_6329_;
}
else
{
lean_object* v_reuseFailAlloc_6331_; 
v_reuseFailAlloc_6331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6331_, 0, v___x_6327_);
lean_ctor_set(v_reuseFailAlloc_6331_, 1, v___x_6328_);
v___x_6330_ = v_reuseFailAlloc_6331_;
goto v_reusejp_6329_;
}
v_reusejp_6329_:
{
return v___x_6330_;
}
}
else
{
lean_object* v_k_x27_6332_; uint8_t v___x_6333_; 
v_k_x27_6332_ = lean_array_fget_borrowed(v_ks_6320_, v_x_6317_);
v___x_6333_ = l_Lean_instBEqMVarId_beq(v_x_6318_, v_k_x27_6332_);
if (v___x_6333_ == 0)
{
lean_object* v___x_6335_; 
if (v_isShared_6324_ == 0)
{
v___x_6335_ = v___x_6323_;
goto v_reusejp_6334_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_ks_6320_);
lean_ctor_set(v_reuseFailAlloc_6339_, 1, v_vs_6321_);
v___x_6335_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6334_;
}
v_reusejp_6334_:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6336_ = lean_unsigned_to_nat(1u);
v___x_6337_ = lean_nat_add(v_x_6317_, v___x_6336_);
lean_dec(v_x_6317_);
v_x_6316_ = v___x_6335_;
v_x_6317_ = v___x_6337_;
goto _start;
}
}
else
{
lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6343_; 
v___x_6340_ = lean_array_fset(v_ks_6320_, v_x_6317_, v_x_6318_);
v___x_6341_ = lean_array_fset(v_vs_6321_, v_x_6317_, v_x_6319_);
lean_dec(v_x_6317_);
if (v_isShared_6324_ == 0)
{
lean_ctor_set(v___x_6323_, 1, v___x_6341_);
lean_ctor_set(v___x_6323_, 0, v___x_6340_);
v___x_6343_ = v___x_6323_;
goto v_reusejp_6342_;
}
else
{
lean_object* v_reuseFailAlloc_6344_; 
v_reuseFailAlloc_6344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6344_, 0, v___x_6340_);
lean_ctor_set(v_reuseFailAlloc_6344_, 1, v___x_6341_);
v___x_6343_ = v_reuseFailAlloc_6344_;
goto v_reusejp_6342_;
}
v_reusejp_6342_:
{
return v___x_6343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(lean_object* v_n_6346_, lean_object* v_k_6347_, lean_object* v_v_6348_){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6349_ = lean_unsigned_to_nat(0u);
v___x_6350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_n_6346_, v___x_6349_, v_k_6347_, v_v_6348_);
return v___x_6350_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_6351_; 
v___x_6351_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(lean_object* v_x_6352_, size_t v_x_6353_, size_t v_x_6354_, lean_object* v_x_6355_, lean_object* v_x_6356_){
_start:
{
if (lean_obj_tag(v_x_6352_) == 0)
{
lean_object* v_es_6357_; size_t v___x_6358_; size_t v___x_6359_; lean_object* v_j_6360_; lean_object* v___x_6361_; uint8_t v___x_6362_; 
v_es_6357_ = lean_ctor_get(v_x_6352_, 0);
v___x_6358_ = ((size_t)31ULL);
v___x_6359_ = lean_usize_land(v_x_6353_, v___x_6358_);
v_j_6360_ = lean_usize_to_nat(v___x_6359_);
v___x_6361_ = lean_array_get_size(v_es_6357_);
v___x_6362_ = lean_nat_dec_lt(v_j_6360_, v___x_6361_);
if (v___x_6362_ == 0)
{
lean_dec(v_j_6360_);
lean_dec(v_x_6356_);
lean_dec(v_x_6355_);
return v_x_6352_;
}
else
{
lean_object* v___x_6364_; uint8_t v_isShared_6365_; uint8_t v_isSharedCheck_6401_; 
lean_inc_ref(v_es_6357_);
v_isSharedCheck_6401_ = !lean_is_exclusive(v_x_6352_);
if (v_isSharedCheck_6401_ == 0)
{
lean_object* v_unused_6402_; 
v_unused_6402_ = lean_ctor_get(v_x_6352_, 0);
lean_dec(v_unused_6402_);
v___x_6364_ = v_x_6352_;
v_isShared_6365_ = v_isSharedCheck_6401_;
goto v_resetjp_6363_;
}
else
{
lean_dec(v_x_6352_);
v___x_6364_ = lean_box(0);
v_isShared_6365_ = v_isSharedCheck_6401_;
goto v_resetjp_6363_;
}
v_resetjp_6363_:
{
lean_object* v_v_6366_; lean_object* v___x_6367_; lean_object* v_xs_x27_6368_; lean_object* v___y_6370_; 
v_v_6366_ = lean_array_fget(v_es_6357_, v_j_6360_);
v___x_6367_ = lean_box(0);
v_xs_x27_6368_ = lean_array_fset(v_es_6357_, v_j_6360_, v___x_6367_);
switch(lean_obj_tag(v_v_6366_))
{
case 0:
{
lean_object* v_key_6375_; lean_object* v_val_6376_; lean_object* v___x_6378_; uint8_t v_isShared_6379_; uint8_t v_isSharedCheck_6386_; 
v_key_6375_ = lean_ctor_get(v_v_6366_, 0);
v_val_6376_ = lean_ctor_get(v_v_6366_, 1);
v_isSharedCheck_6386_ = !lean_is_exclusive(v_v_6366_);
if (v_isSharedCheck_6386_ == 0)
{
v___x_6378_ = v_v_6366_;
v_isShared_6379_ = v_isSharedCheck_6386_;
goto v_resetjp_6377_;
}
else
{
lean_inc(v_val_6376_);
lean_inc(v_key_6375_);
lean_dec(v_v_6366_);
v___x_6378_ = lean_box(0);
v_isShared_6379_ = v_isSharedCheck_6386_;
goto v_resetjp_6377_;
}
v_resetjp_6377_:
{
uint8_t v___x_6380_; 
v___x_6380_ = l_Lean_instBEqMVarId_beq(v_x_6355_, v_key_6375_);
if (v___x_6380_ == 0)
{
lean_object* v___x_6381_; lean_object* v___x_6382_; 
lean_del_object(v___x_6378_);
v___x_6381_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_6375_, v_val_6376_, v_x_6355_, v_x_6356_);
v___x_6382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6382_, 0, v___x_6381_);
v___y_6370_ = v___x_6382_;
goto v___jp_6369_;
}
else
{
lean_object* v___x_6384_; 
lean_dec(v_val_6376_);
lean_dec(v_key_6375_);
if (v_isShared_6379_ == 0)
{
lean_ctor_set(v___x_6378_, 1, v_x_6356_);
lean_ctor_set(v___x_6378_, 0, v_x_6355_);
v___x_6384_ = v___x_6378_;
goto v_reusejp_6383_;
}
else
{
lean_object* v_reuseFailAlloc_6385_; 
v_reuseFailAlloc_6385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6385_, 0, v_x_6355_);
lean_ctor_set(v_reuseFailAlloc_6385_, 1, v_x_6356_);
v___x_6384_ = v_reuseFailAlloc_6385_;
goto v_reusejp_6383_;
}
v_reusejp_6383_:
{
v___y_6370_ = v___x_6384_;
goto v___jp_6369_;
}
}
}
}
case 1:
{
lean_object* v_node_6387_; lean_object* v___x_6389_; uint8_t v_isShared_6390_; uint8_t v_isSharedCheck_6399_; 
v_node_6387_ = lean_ctor_get(v_v_6366_, 0);
v_isSharedCheck_6399_ = !lean_is_exclusive(v_v_6366_);
if (v_isSharedCheck_6399_ == 0)
{
v___x_6389_ = v_v_6366_;
v_isShared_6390_ = v_isSharedCheck_6399_;
goto v_resetjp_6388_;
}
else
{
lean_inc(v_node_6387_);
lean_dec(v_v_6366_);
v___x_6389_ = lean_box(0);
v_isShared_6390_ = v_isSharedCheck_6399_;
goto v_resetjp_6388_;
}
v_resetjp_6388_:
{
size_t v___x_6391_; size_t v___x_6392_; size_t v___x_6393_; size_t v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6397_; 
v___x_6391_ = ((size_t)5ULL);
v___x_6392_ = lean_usize_shift_right(v_x_6353_, v___x_6391_);
v___x_6393_ = ((size_t)1ULL);
v___x_6394_ = lean_usize_add(v_x_6354_, v___x_6393_);
v___x_6395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_node_6387_, v___x_6392_, v___x_6394_, v_x_6355_, v_x_6356_);
if (v_isShared_6390_ == 0)
{
lean_ctor_set(v___x_6389_, 0, v___x_6395_);
v___x_6397_ = v___x_6389_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6398_; 
v_reuseFailAlloc_6398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6398_, 0, v___x_6395_);
v___x_6397_ = v_reuseFailAlloc_6398_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
v___y_6370_ = v___x_6397_;
goto v___jp_6369_;
}
}
}
default: 
{
lean_object* v___x_6400_; 
v___x_6400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6400_, 0, v_x_6355_);
lean_ctor_set(v___x_6400_, 1, v_x_6356_);
v___y_6370_ = v___x_6400_;
goto v___jp_6369_;
}
}
v___jp_6369_:
{
lean_object* v___x_6371_; lean_object* v___x_6373_; 
v___x_6371_ = lean_array_fset(v_xs_x27_6368_, v_j_6360_, v___y_6370_);
lean_dec(v_j_6360_);
if (v_isShared_6365_ == 0)
{
lean_ctor_set(v___x_6364_, 0, v___x_6371_);
v___x_6373_ = v___x_6364_;
goto v_reusejp_6372_;
}
else
{
lean_object* v_reuseFailAlloc_6374_; 
v_reuseFailAlloc_6374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6374_, 0, v___x_6371_);
v___x_6373_ = v_reuseFailAlloc_6374_;
goto v_reusejp_6372_;
}
v_reusejp_6372_:
{
return v___x_6373_;
}
}
}
}
}
else
{
lean_object* v_ks_6403_; lean_object* v_vs_6404_; lean_object* v___x_6406_; uint8_t v_isShared_6407_; uint8_t v_isSharedCheck_6422_; 
v_ks_6403_ = lean_ctor_get(v_x_6352_, 0);
v_vs_6404_ = lean_ctor_get(v_x_6352_, 1);
v_isSharedCheck_6422_ = !lean_is_exclusive(v_x_6352_);
if (v_isSharedCheck_6422_ == 0)
{
v___x_6406_ = v_x_6352_;
v_isShared_6407_ = v_isSharedCheck_6422_;
goto v_resetjp_6405_;
}
else
{
lean_inc(v_vs_6404_);
lean_inc(v_ks_6403_);
lean_dec(v_x_6352_);
v___x_6406_ = lean_box(0);
v_isShared_6407_ = v_isSharedCheck_6422_;
goto v_resetjp_6405_;
}
v_resetjp_6405_:
{
lean_object* v___x_6409_; 
if (v_isShared_6407_ == 0)
{
v___x_6409_ = v___x_6406_;
goto v_reusejp_6408_;
}
else
{
lean_object* v_reuseFailAlloc_6421_; 
v_reuseFailAlloc_6421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6421_, 0, v_ks_6403_);
lean_ctor_set(v_reuseFailAlloc_6421_, 1, v_vs_6404_);
v___x_6409_ = v_reuseFailAlloc_6421_;
goto v_reusejp_6408_;
}
v_reusejp_6408_:
{
lean_object* v_newNode_6410_; size_t v___x_6411_; uint8_t v___x_6412_; 
v_newNode_6410_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v___x_6409_, v_x_6355_, v_x_6356_);
v___x_6411_ = ((size_t)7ULL);
v___x_6412_ = lean_usize_dec_le(v___x_6411_, v_x_6354_);
if (v___x_6412_ == 0)
{
lean_object* v___x_6413_; lean_object* v___x_6414_; uint8_t v___x_6415_; 
v___x_6413_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_6410_);
v___x_6414_ = lean_unsigned_to_nat(4u);
v___x_6415_ = lean_nat_dec_lt(v___x_6413_, v___x_6414_);
lean_dec(v___x_6413_);
if (v___x_6415_ == 0)
{
lean_object* v_ks_6416_; lean_object* v_vs_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; 
v_ks_6416_ = lean_ctor_get(v_newNode_6410_, 0);
lean_inc_ref(v_ks_6416_);
v_vs_6417_ = lean_ctor_get(v_newNode_6410_, 1);
lean_inc_ref(v_vs_6417_);
lean_dec_ref(v_newNode_6410_);
v___x_6418_ = lean_unsigned_to_nat(0u);
v___x_6419_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0);
v___x_6420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_x_6354_, v_ks_6416_, v_vs_6417_, v___x_6418_, v___x_6419_);
lean_dec_ref(v_vs_6417_);
lean_dec_ref(v_ks_6416_);
return v___x_6420_;
}
else
{
return v_newNode_6410_;
}
}
else
{
return v_newNode_6410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(size_t v_depth_6423_, lean_object* v_keys_6424_, lean_object* v_vals_6425_, lean_object* v_i_6426_, lean_object* v_entries_6427_){
_start:
{
lean_object* v___x_6428_; uint8_t v___x_6429_; 
v___x_6428_ = lean_array_get_size(v_keys_6424_);
v___x_6429_ = lean_nat_dec_lt(v_i_6426_, v___x_6428_);
if (v___x_6429_ == 0)
{
lean_dec(v_i_6426_);
return v_entries_6427_;
}
else
{
lean_object* v_k_6430_; lean_object* v_v_6431_; uint64_t v___x_6432_; size_t v_h_6433_; size_t v___x_6434_; lean_object* v___x_6435_; size_t v___x_6436_; size_t v___x_6437_; size_t v___x_6438_; size_t v_h_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
v_k_6430_ = lean_array_fget_borrowed(v_keys_6424_, v_i_6426_);
v_v_6431_ = lean_array_fget_borrowed(v_vals_6425_, v_i_6426_);
v___x_6432_ = l_Lean_instHashableMVarId_hash(v_k_6430_);
v_h_6433_ = lean_uint64_to_usize(v___x_6432_);
v___x_6434_ = ((size_t)5ULL);
v___x_6435_ = lean_unsigned_to_nat(1u);
v___x_6436_ = ((size_t)1ULL);
v___x_6437_ = lean_usize_sub(v_depth_6423_, v___x_6436_);
v___x_6438_ = lean_usize_mul(v___x_6434_, v___x_6437_);
v_h_6439_ = lean_usize_shift_right(v_h_6433_, v___x_6438_);
v___x_6440_ = lean_nat_add(v_i_6426_, v___x_6435_);
lean_dec(v_i_6426_);
lean_inc(v_v_6431_);
lean_inc(v_k_6430_);
v___x_6441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_entries_6427_, v_h_6439_, v_depth_6423_, v_k_6430_, v_v_6431_);
v_i_6426_ = v___x_6440_;
v_entries_6427_ = v___x_6441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_depth_6443_, lean_object* v_keys_6444_, lean_object* v_vals_6445_, lean_object* v_i_6446_, lean_object* v_entries_6447_){
_start:
{
size_t v_depth_boxed_6448_; lean_object* v_res_6449_; 
v_depth_boxed_6448_ = lean_unbox_usize(v_depth_6443_);
lean_dec(v_depth_6443_);
v_res_6449_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_boxed_6448_, v_keys_6444_, v_vals_6445_, v_i_6446_, v_entries_6447_);
lean_dec_ref(v_vals_6445_);
lean_dec_ref(v_keys_6444_);
return v_res_6449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_x_6450_, lean_object* v_x_6451_, lean_object* v_x_6452_, lean_object* v_x_6453_, lean_object* v_x_6454_){
_start:
{
size_t v_x_118201__boxed_6455_; size_t v_x_118202__boxed_6456_; lean_object* v_res_6457_; 
v_x_118201__boxed_6455_ = lean_unbox_usize(v_x_6451_);
lean_dec(v_x_6451_);
v_x_118202__boxed_6456_ = lean_unbox_usize(v_x_6452_);
lean_dec(v_x_6452_);
v_res_6457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6450_, v_x_118201__boxed_6455_, v_x_118202__boxed_6456_, v_x_6453_, v_x_6454_);
return v_res_6457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(lean_object* v_x_6458_, lean_object* v_x_6459_, lean_object* v_x_6460_){
_start:
{
uint64_t v___x_6461_; size_t v___x_6462_; size_t v___x_6463_; lean_object* v___x_6464_; 
v___x_6461_ = l_Lean_instHashableMVarId_hash(v_x_6459_);
v___x_6462_ = lean_uint64_to_usize(v___x_6461_);
v___x_6463_ = ((size_t)1ULL);
v___x_6464_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6458_, v___x_6462_, v___x_6463_, v_x_6459_, v_x_6460_);
return v___x_6464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_mvarId_6465_, lean_object* v_val_6466_, lean_object* v___y_6467_){
_start:
{
lean_object* v___x_6469_; lean_object* v_mctx_6470_; lean_object* v_cache_6471_; lean_object* v_zetaDeltaFVarIds_6472_; lean_object* v_postponed_6473_; lean_object* v_diag_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6502_; 
v___x_6469_ = lean_st_ref_take(v___y_6467_);
v_mctx_6470_ = lean_ctor_get(v___x_6469_, 0);
v_cache_6471_ = lean_ctor_get(v___x_6469_, 1);
v_zetaDeltaFVarIds_6472_ = lean_ctor_get(v___x_6469_, 2);
v_postponed_6473_ = lean_ctor_get(v___x_6469_, 3);
v_diag_6474_ = lean_ctor_get(v___x_6469_, 4);
v_isSharedCheck_6502_ = !lean_is_exclusive(v___x_6469_);
if (v_isSharedCheck_6502_ == 0)
{
v___x_6476_ = v___x_6469_;
v_isShared_6477_ = v_isSharedCheck_6502_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_diag_6474_);
lean_inc(v_postponed_6473_);
lean_inc(v_zetaDeltaFVarIds_6472_);
lean_inc(v_cache_6471_);
lean_inc(v_mctx_6470_);
lean_dec(v___x_6469_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6502_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v_depth_6478_; lean_object* v_levelAssignDepth_6479_; lean_object* v_lmvarCounter_6480_; lean_object* v_mvarCounter_6481_; lean_object* v_lDecls_6482_; lean_object* v_decls_6483_; lean_object* v_userNames_6484_; lean_object* v_lAssignment_6485_; lean_object* v_eAssignment_6486_; lean_object* v_dAssignment_6487_; lean_object* v___x_6489_; uint8_t v_isShared_6490_; uint8_t v_isSharedCheck_6501_; 
v_depth_6478_ = lean_ctor_get(v_mctx_6470_, 0);
v_levelAssignDepth_6479_ = lean_ctor_get(v_mctx_6470_, 1);
v_lmvarCounter_6480_ = lean_ctor_get(v_mctx_6470_, 2);
v_mvarCounter_6481_ = lean_ctor_get(v_mctx_6470_, 3);
v_lDecls_6482_ = lean_ctor_get(v_mctx_6470_, 4);
v_decls_6483_ = lean_ctor_get(v_mctx_6470_, 5);
v_userNames_6484_ = lean_ctor_get(v_mctx_6470_, 6);
v_lAssignment_6485_ = lean_ctor_get(v_mctx_6470_, 7);
v_eAssignment_6486_ = lean_ctor_get(v_mctx_6470_, 8);
v_dAssignment_6487_ = lean_ctor_get(v_mctx_6470_, 9);
v_isSharedCheck_6501_ = !lean_is_exclusive(v_mctx_6470_);
if (v_isSharedCheck_6501_ == 0)
{
v___x_6489_ = v_mctx_6470_;
v_isShared_6490_ = v_isSharedCheck_6501_;
goto v_resetjp_6488_;
}
else
{
lean_inc(v_dAssignment_6487_);
lean_inc(v_eAssignment_6486_);
lean_inc(v_lAssignment_6485_);
lean_inc(v_userNames_6484_);
lean_inc(v_decls_6483_);
lean_inc(v_lDecls_6482_);
lean_inc(v_mvarCounter_6481_);
lean_inc(v_lmvarCounter_6480_);
lean_inc(v_levelAssignDepth_6479_);
lean_inc(v_depth_6478_);
lean_dec(v_mctx_6470_);
v___x_6489_ = lean_box(0);
v_isShared_6490_ = v_isSharedCheck_6501_;
goto v_resetjp_6488_;
}
v_resetjp_6488_:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6494_; 
v___x_6491_ = lean_box(0);
v___x_6492_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_eAssignment_6486_, v_mvarId_6465_, v_val_6466_);
if (v_isShared_6490_ == 0)
{
lean_ctor_set(v___x_6489_, 8, v___x_6492_);
v___x_6494_ = v___x_6489_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6500_; 
v_reuseFailAlloc_6500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6500_, 0, v_depth_6478_);
lean_ctor_set(v_reuseFailAlloc_6500_, 1, v_levelAssignDepth_6479_);
lean_ctor_set(v_reuseFailAlloc_6500_, 2, v_lmvarCounter_6480_);
lean_ctor_set(v_reuseFailAlloc_6500_, 3, v_mvarCounter_6481_);
lean_ctor_set(v_reuseFailAlloc_6500_, 4, v_lDecls_6482_);
lean_ctor_set(v_reuseFailAlloc_6500_, 5, v_decls_6483_);
lean_ctor_set(v_reuseFailAlloc_6500_, 6, v_userNames_6484_);
lean_ctor_set(v_reuseFailAlloc_6500_, 7, v_lAssignment_6485_);
lean_ctor_set(v_reuseFailAlloc_6500_, 8, v___x_6492_);
lean_ctor_set(v_reuseFailAlloc_6500_, 9, v_dAssignment_6487_);
v___x_6494_ = v_reuseFailAlloc_6500_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
lean_object* v___x_6496_; 
if (v_isShared_6477_ == 0)
{
lean_ctor_set(v___x_6476_, 0, v___x_6494_);
v___x_6496_ = v___x_6476_;
goto v_reusejp_6495_;
}
else
{
lean_object* v_reuseFailAlloc_6499_; 
v_reuseFailAlloc_6499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6499_, 0, v___x_6494_);
lean_ctor_set(v_reuseFailAlloc_6499_, 1, v_cache_6471_);
lean_ctor_set(v_reuseFailAlloc_6499_, 2, v_zetaDeltaFVarIds_6472_);
lean_ctor_set(v_reuseFailAlloc_6499_, 3, v_postponed_6473_);
lean_ctor_set(v_reuseFailAlloc_6499_, 4, v_diag_6474_);
v___x_6496_ = v_reuseFailAlloc_6499_;
goto v_reusejp_6495_;
}
v_reusejp_6495_:
{
lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6497_ = lean_st_ref_put(v___y_6467_, v___x_6496_);
v___x_6498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6498_, 0, v___x_6491_);
return v___x_6498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_mvarId_6503_, lean_object* v_val_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_){
_start:
{
lean_object* v_res_6507_; 
v_res_6507_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6503_, v_val_6504_, v___y_6505_);
lean_dec(v___y_6505_);
return v_res_6507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(lean_object* v_goal_6512_, lean_object* v_c_6513_, lean_object* v_numCases_6514_, uint8_t v_isRec_6515_, lean_object* v_candidates_x3f_6516_, uint8_t v_compress_6517_, lean_object* v_kp_6518_, uint8_t v_stopAtFirstFailure_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_){
_start:
{
lean_object* v___x_6530_; 
v___x_6530_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_6521_);
if (lean_obj_tag(v___x_6530_) == 0)
{
lean_object* v_a_6531_; uint8_t v_trace_6532_; lean_object* v___x_6533_; 
v_a_6531_ = lean_ctor_get(v___x_6530_, 0);
lean_inc(v_a_6531_);
lean_dec_ref_known(v___x_6530_, 1);
v_trace_6532_ = lean_ctor_get_uint8(v_a_6531_, sizeof(void*)*18);
lean_dec(v_a_6531_);
v___x_6533_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v___y_6521_, v___y_6522_, v___y_6526_, v___y_6528_);
if (lean_obj_tag(v___x_6533_) == 0)
{
lean_object* v_a_6534_; lean_object* v___x_6535_; 
v_a_6534_ = lean_ctor_get(v___x_6533_, 0);
lean_inc(v_a_6534_);
lean_dec_ref_known(v___x_6533_, 1);
lean_inc_ref(v_goal_6512_);
v___x_6535_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_6512_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
if (lean_obj_tag(v___x_6535_) == 0)
{
lean_object* v_a_6536_; lean_object* v_mvarId_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___f_6540_; lean_object* v___x_6541_; lean_object* v___f_6542_; lean_object* v___x_6543_; 
v_a_6536_ = lean_ctor_get(v___x_6535_, 0);
lean_inc_n(v_a_6536_, 2);
lean_dec_ref_known(v___x_6535_, 1);
v_mvarId_6537_ = lean_ctor_get(v_goal_6512_, 1);
v___x_6538_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6513_);
v___x_6539_ = lean_box(v_isRec_6515_);
lean_inc_ref_n(v_c_6513_, 2);
lean_inc_ref(v___x_6538_);
v___f_6540_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6540_, 0, v___x_6538_);
lean_closure_set(v___f_6540_, 1, v_c_6513_);
lean_closure_set(v___f_6540_, 2, v_a_6536_);
lean_closure_set(v___f_6540_, 3, v_numCases_6514_);
lean_closure_set(v___f_6540_, 4, v___x_6539_);
v___x_6541_ = lean_box(v_trace_6532_);
lean_inc_ref(v_goal_6512_);
v___f_6542_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_6542_, 0, v_goal_6512_);
lean_closure_set(v___f_6542_, 1, v___x_6541_);
lean_closure_set(v___f_6542_, 2, v___f_6540_);
lean_closure_set(v___f_6542_, 3, v_c_6513_);
lean_closure_set(v___f_6542_, 4, v_candidates_x3f_6516_);
lean_inc(v_mvarId_6537_);
v___x_6543_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6537_, v___f_6542_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
if (lean_obj_tag(v___x_6543_) == 0)
{
lean_object* v_a_6544_; lean_object* v___x_6546_; uint8_t v_isShared_6547_; uint8_t v_isSharedCheck_6723_; 
v_a_6544_ = lean_ctor_get(v___x_6543_, 0);
v_isSharedCheck_6723_ = !lean_is_exclusive(v___x_6543_);
if (v_isSharedCheck_6723_ == 0)
{
v___x_6546_ = v___x_6543_;
v_isShared_6547_ = v_isSharedCheck_6723_;
goto v_resetjp_6545_;
}
else
{
lean_inc(v_a_6544_);
lean_dec(v___x_6543_);
v___x_6546_ = lean_box(0);
v_isShared_6547_ = v_isSharedCheck_6723_;
goto v_resetjp_6545_;
}
v_resetjp_6545_:
{
lean_object* v_fst_6548_; lean_object* v_snd_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6722_; 
v_fst_6548_ = lean_ctor_get(v_a_6544_, 0);
v_snd_6549_ = lean_ctor_get(v_a_6544_, 1);
v_isSharedCheck_6722_ = !lean_is_exclusive(v_a_6544_);
if (v_isSharedCheck_6722_ == 0)
{
v___x_6551_ = v_a_6544_;
v_isShared_6552_ = v_isSharedCheck_6722_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_snd_6549_);
lean_inc(v_fst_6548_);
lean_dec(v_a_6544_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6722_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v_fst_6553_; lean_object* v_snd_6554_; lean_object* v___x_6556_; uint8_t v_isShared_6557_; uint8_t v_isSharedCheck_6721_; 
v_fst_6553_ = lean_ctor_get(v_fst_6548_, 0);
v_snd_6554_ = lean_ctor_get(v_fst_6548_, 1);
v_isSharedCheck_6721_ = !lean_is_exclusive(v_fst_6548_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6556_ = v_fst_6548_;
v_isShared_6557_ = v_isSharedCheck_6721_;
goto v_resetjp_6555_;
}
else
{
lean_inc(v_snd_6554_);
lean_inc(v_fst_6553_);
lean_dec(v_fst_6548_);
v___x_6556_ = lean_box(0);
v_isShared_6557_ = v_isSharedCheck_6721_;
goto v_resetjp_6555_;
}
v_resetjp_6555_:
{
lean_object* v___y_6559_; lean_object* v___y_6560_; lean_object* v___y_6561_; lean_object* v___y_6562_; lean_object* v___y_6563_; lean_object* v___f_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v_congrThms_6613_; lean_object* v_simp_6614_; lean_object* v_symSimp_6615_; lean_object* v_symDSimp_6616_; lean_object* v_lastTag_6617_; lean_object* v_counters_6618_; lean_object* v_splitDiags_6619_; lean_object* v_ematchDiags_6620_; lean_object* v_lawfulEqCmpMap_6621_; lean_object* v_reflCmpMap_6622_; lean_object* v_anchors_6623_; lean_object* v_fvarAnchors_6624_; lean_object* v_instanceMap_6625_; lean_object* v_hoistedDecls_6626_; lean_object* v_proofInfos_6627_; lean_object* v_numBranches_6628_; lean_object* v___x_6630_; uint8_t v_isShared_6631_; uint8_t v_isSharedCheck_6720_; 
lean_inc(v_snd_6549_);
v___f_6610_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed), 12, 2);
lean_closure_set(v___f_6610_, 0, v_snd_6549_);
lean_closure_set(v___f_6610_, 1, v_a_6536_);
v___x_6611_ = l_List_lengthTR___redArg(v_fst_6553_);
v___x_6612_ = lean_st_ref_take(v___y_6522_);
v_congrThms_6613_ = lean_ctor_get(v___x_6612_, 0);
v_simp_6614_ = lean_ctor_get(v___x_6612_, 1);
v_symSimp_6615_ = lean_ctor_get(v___x_6612_, 2);
v_symDSimp_6616_ = lean_ctor_get(v___x_6612_, 3);
v_lastTag_6617_ = lean_ctor_get(v___x_6612_, 4);
v_counters_6618_ = lean_ctor_get(v___x_6612_, 5);
v_splitDiags_6619_ = lean_ctor_get(v___x_6612_, 6);
v_ematchDiags_6620_ = lean_ctor_get(v___x_6612_, 7);
v_lawfulEqCmpMap_6621_ = lean_ctor_get(v___x_6612_, 8);
v_reflCmpMap_6622_ = lean_ctor_get(v___x_6612_, 9);
v_anchors_6623_ = lean_ctor_get(v___x_6612_, 10);
v_fvarAnchors_6624_ = lean_ctor_get(v___x_6612_, 11);
v_instanceMap_6625_ = lean_ctor_get(v___x_6612_, 12);
v_hoistedDecls_6626_ = lean_ctor_get(v___x_6612_, 13);
v_proofInfos_6627_ = lean_ctor_get(v___x_6612_, 14);
v_numBranches_6628_ = lean_ctor_get(v___x_6612_, 15);
v_isSharedCheck_6720_ = !lean_is_exclusive(v___x_6612_);
if (v_isSharedCheck_6720_ == 0)
{
v___x_6630_ = v___x_6612_;
v_isShared_6631_ = v_isSharedCheck_6720_;
goto v_resetjp_6629_;
}
else
{
lean_inc(v_numBranches_6628_);
lean_inc(v_proofInfos_6627_);
lean_inc(v_hoistedDecls_6626_);
lean_inc(v_instanceMap_6625_);
lean_inc(v_fvarAnchors_6624_);
lean_inc(v_anchors_6623_);
lean_inc(v_reflCmpMap_6622_);
lean_inc(v_lawfulEqCmpMap_6621_);
lean_inc(v_ematchDiags_6620_);
lean_inc(v_splitDiags_6619_);
lean_inc(v_counters_6618_);
lean_inc(v_lastTag_6617_);
lean_inc(v_symDSimp_6616_);
lean_inc(v_symSimp_6615_);
lean_inc(v_simp_6614_);
lean_inc(v_congrThms_6613_);
lean_dec(v___x_6612_);
v___x_6630_ = lean_box(0);
v_isShared_6631_ = v_isSharedCheck_6720_;
goto v_resetjp_6629_;
}
v___jp_6558_:
{
lean_object* v___x_6564_; uint8_t v___x_6565_; 
v___x_6564_ = lean_array_get_size(v___y_6559_);
v___x_6565_ = lean_nat_dec_eq(v___x_6564_, v___y_6561_);
if (v___x_6565_ == 0)
{
lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6569_; 
lean_dec(v___y_6560_);
lean_dec(v_snd_6554_);
v___x_6566_ = lean_array_to_list(v___y_6559_);
v___x_6567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6567_, 0, v___x_6566_);
if (v_isShared_6547_ == 0)
{
lean_ctor_set(v___x_6546_, 0, v___x_6567_);
v___x_6569_ = v___x_6546_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v___x_6567_);
v___x_6569_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
return v___x_6569_;
}
}
else
{
lean_dec(v___y_6559_);
if (lean_obj_tag(v_snd_6554_) == 1)
{
lean_object* v_val_6571_; lean_object* v___x_6573_; uint8_t v_isShared_6574_; uint8_t v_isSharedCheck_6605_; 
lean_del_object(v___x_6546_);
v_val_6571_ = lean_ctor_get(v_snd_6554_, 0);
v_isSharedCheck_6605_ = !lean_is_exclusive(v_snd_6554_);
if (v_isSharedCheck_6605_ == 0)
{
v___x_6573_ = v_snd_6554_;
v_isShared_6574_ = v_isSharedCheck_6605_;
goto v_resetjp_6572_;
}
else
{
lean_inc(v_val_6571_);
lean_dec(v_snd_6554_);
v___x_6573_ = lean_box(0);
v_isShared_6574_ = v_isSharedCheck_6605_;
goto v_resetjp_6572_;
}
v_resetjp_6572_:
{
lean_object* v___x_6575_; 
v___x_6575_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_6571_, v___y_6562_);
lean_dec(v_val_6571_);
if (lean_obj_tag(v___x_6575_) == 0)
{
lean_object* v_a_6576_; lean_object* v___x_6577_; 
v_a_6576_ = lean_ctor_get(v___x_6575_, 0);
lean_inc(v_a_6576_);
lean_dec_ref_known(v___x_6575_, 1);
v___x_6577_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_6576_, v___y_6560_, v_compress_6517_, v___y_6562_, v___y_6563_);
if (lean_obj_tag(v___x_6577_) == 0)
{
lean_object* v_a_6578_; lean_object* v___x_6580_; uint8_t v_isShared_6581_; uint8_t v_isSharedCheck_6588_; 
v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6580_ = v___x_6577_;
v_isShared_6581_ = v_isSharedCheck_6588_;
goto v_resetjp_6579_;
}
else
{
lean_inc(v_a_6578_);
lean_dec(v___x_6577_);
v___x_6580_ = lean_box(0);
v_isShared_6581_ = v_isSharedCheck_6588_;
goto v_resetjp_6579_;
}
v_resetjp_6579_:
{
lean_object* v___x_6583_; 
if (v_isShared_6574_ == 0)
{
lean_ctor_set_tag(v___x_6573_, 0);
lean_ctor_set(v___x_6573_, 0, v_a_6578_);
v___x_6583_ = v___x_6573_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v_a_6578_);
v___x_6583_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
lean_object* v___x_6585_; 
if (v_isShared_6581_ == 0)
{
lean_ctor_set(v___x_6580_, 0, v___x_6583_);
v___x_6585_ = v___x_6580_;
goto v_reusejp_6584_;
}
else
{
lean_object* v_reuseFailAlloc_6586_; 
v_reuseFailAlloc_6586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6586_, 0, v___x_6583_);
v___x_6585_ = v_reuseFailAlloc_6586_;
goto v_reusejp_6584_;
}
v_reusejp_6584_:
{
return v___x_6585_;
}
}
}
}
else
{
lean_object* v_a_6589_; lean_object* v___x_6591_; uint8_t v_isShared_6592_; uint8_t v_isSharedCheck_6596_; 
lean_del_object(v___x_6573_);
v_a_6589_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6596_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6596_ == 0)
{
v___x_6591_ = v___x_6577_;
v_isShared_6592_ = v_isSharedCheck_6596_;
goto v_resetjp_6590_;
}
else
{
lean_inc(v_a_6589_);
lean_dec(v___x_6577_);
v___x_6591_ = lean_box(0);
v_isShared_6592_ = v_isSharedCheck_6596_;
goto v_resetjp_6590_;
}
v_resetjp_6590_:
{
lean_object* v___x_6594_; 
if (v_isShared_6592_ == 0)
{
v___x_6594_ = v___x_6591_;
goto v_reusejp_6593_;
}
else
{
lean_object* v_reuseFailAlloc_6595_; 
v_reuseFailAlloc_6595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6595_, 0, v_a_6589_);
v___x_6594_ = v_reuseFailAlloc_6595_;
goto v_reusejp_6593_;
}
v_reusejp_6593_:
{
return v___x_6594_;
}
}
}
}
else
{
lean_object* v_a_6597_; lean_object* v___x_6599_; uint8_t v_isShared_6600_; uint8_t v_isSharedCheck_6604_; 
lean_del_object(v___x_6573_);
lean_dec(v___y_6560_);
v_a_6597_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6604_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6604_ == 0)
{
v___x_6599_ = v___x_6575_;
v_isShared_6600_ = v_isSharedCheck_6604_;
goto v_resetjp_6598_;
}
else
{
lean_inc(v_a_6597_);
lean_dec(v___x_6575_);
v___x_6599_ = lean_box(0);
v_isShared_6600_ = v_isSharedCheck_6604_;
goto v_resetjp_6598_;
}
v_resetjp_6598_:
{
lean_object* v___x_6602_; 
if (v_isShared_6600_ == 0)
{
v___x_6602_ = v___x_6599_;
goto v_reusejp_6601_;
}
else
{
lean_object* v_reuseFailAlloc_6603_; 
v_reuseFailAlloc_6603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6603_, 0, v_a_6597_);
v___x_6602_ = v_reuseFailAlloc_6603_;
goto v_reusejp_6601_;
}
v_reusejp_6601_:
{
return v___x_6602_;
}
}
}
}
}
else
{
lean_object* v___x_6606_; lean_object* v___x_6608_; 
lean_dec(v___y_6560_);
lean_dec(v_snd_6554_);
v___x_6606_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0));
if (v_isShared_6547_ == 0)
{
lean_ctor_set(v___x_6546_, 0, v___x_6606_);
v___x_6608_ = v___x_6546_;
goto v_reusejp_6607_;
}
else
{
lean_object* v_reuseFailAlloc_6609_; 
v_reuseFailAlloc_6609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6609_, 0, v___x_6606_);
v___x_6608_ = v_reuseFailAlloc_6609_;
goto v_reusejp_6607_;
}
v_reusejp_6607_:
{
return v___x_6608_;
}
}
}
}
v_resetjp_6629_:
{
lean_object* v___y_6633_; 
if (v_isRec_6515_ == 0)
{
lean_object* v___x_6718_; lean_object* v___x_6719_; 
v___x_6718_ = lean_unsigned_to_nat(1u);
v___x_6719_ = lean_nat_sub(v___x_6611_, v___x_6718_);
v___y_6633_ = v___x_6719_;
goto v___jp_6632_;
}
else
{
lean_inc(v___x_6611_);
v___y_6633_ = v___x_6611_;
goto v___jp_6632_;
}
v___jp_6632_:
{
lean_object* v___x_6634_; lean_object* v___x_6636_; 
v___x_6634_ = lean_nat_add(v_numBranches_6628_, v___y_6633_);
lean_dec(v___y_6633_);
lean_dec(v_numBranches_6628_);
if (v_isShared_6631_ == 0)
{
lean_ctor_set(v___x_6630_, 15, v___x_6634_);
v___x_6636_ = v___x_6630_;
goto v_reusejp_6635_;
}
else
{
lean_object* v_reuseFailAlloc_6717_; 
v_reuseFailAlloc_6717_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_6717_, 0, v_congrThms_6613_);
lean_ctor_set(v_reuseFailAlloc_6717_, 1, v_simp_6614_);
lean_ctor_set(v_reuseFailAlloc_6717_, 2, v_symSimp_6615_);
lean_ctor_set(v_reuseFailAlloc_6717_, 3, v_symDSimp_6616_);
lean_ctor_set(v_reuseFailAlloc_6717_, 4, v_lastTag_6617_);
lean_ctor_set(v_reuseFailAlloc_6717_, 5, v_counters_6618_);
lean_ctor_set(v_reuseFailAlloc_6717_, 6, v_splitDiags_6619_);
lean_ctor_set(v_reuseFailAlloc_6717_, 7, v_ematchDiags_6620_);
lean_ctor_set(v_reuseFailAlloc_6717_, 8, v_lawfulEqCmpMap_6621_);
lean_ctor_set(v_reuseFailAlloc_6717_, 9, v_reflCmpMap_6622_);
lean_ctor_set(v_reuseFailAlloc_6717_, 10, v_anchors_6623_);
lean_ctor_set(v_reuseFailAlloc_6717_, 11, v_fvarAnchors_6624_);
lean_ctor_set(v_reuseFailAlloc_6717_, 12, v_instanceMap_6625_);
lean_ctor_set(v_reuseFailAlloc_6717_, 13, v_hoistedDecls_6626_);
lean_ctor_set(v_reuseFailAlloc_6717_, 14, v_proofInfos_6627_);
lean_ctor_set(v_reuseFailAlloc_6717_, 15, v___x_6634_);
v___x_6636_ = v_reuseFailAlloc_6717_;
goto v_reusejp_6635_;
}
v_reusejp_6635_:
{
lean_object* v___x_6637_; lean_object* v_toGoalState_6638_; lean_object* v_mvarId_6639_; lean_object* v_goalStack_6640_; lean_object* v___x_6642_; 
v___x_6637_ = lean_st_ref_put(v___y_6522_, v___x_6636_);
v_toGoalState_6638_ = lean_ctor_get(v_snd_6549_, 0);
v_mvarId_6639_ = lean_ctor_get(v_snd_6549_, 1);
lean_inc_n(v_mvarId_6639_, 2);
v_goalStack_6640_ = lean_ctor_get(v_toGoalState_6638_, 18);
lean_inc_ref(v_goalStack_6640_);
lean_inc_ref(v_toGoalState_6638_);
if (v_isShared_6557_ == 0)
{
lean_ctor_set(v___x_6556_, 1, v_toGoalState_6638_);
lean_ctor_set(v___x_6556_, 0, v_mvarId_6639_);
v___x_6642_ = v___x_6556_;
goto v_reusejp_6641_;
}
else
{
lean_object* v_reuseFailAlloc_6716_; 
v_reuseFailAlloc_6716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_mvarId_6639_);
lean_ctor_set(v_reuseFailAlloc_6716_, 1, v_toGoalState_6638_);
v___x_6642_ = v_reuseFailAlloc_6716_;
goto v_reusejp_6641_;
}
v_reusejp_6641_:
{
lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
lean_inc_ref(v_goalStack_6640_);
v___x_6643_ = lean_array_push(v_goalStack_6640_, v___x_6642_);
lean_inc_ref(v_c_6513_);
v___x_6644_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_6644_, 0, v_c_6513_);
lean_inc(v_mvarId_6639_);
v___x_6645_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6639_, v___x_6644_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
if (lean_obj_tag(v___x_6645_) == 0)
{
lean_object* v_a_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; uint64_t v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6655_; 
v_a_6646_ = lean_ctor_get(v___x_6645_, 0);
lean_inc(v_a_6646_);
lean_dec_ref_known(v___x_6645_, 1);
v___x_6647_ = lean_unsigned_to_nat(0u);
v___x_6648_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1));
v___x_6649_ = lean_unbox_uint64(v_a_6646_);
lean_dec(v_a_6646_);
lean_inc_n(v___x_6611_, 2);
lean_inc_ref(v_toGoalState_6638_);
v___x_6650_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_toGoalState_6638_, v_c_6513_, v___x_6538_, v___x_6611_, v___x_6643_, v___x_6649_, v_fst_6553_, v___x_6648_);
lean_dec_ref(v_c_6513_);
v___x_6651_ = lean_box(0);
v___x_6652_ = lean_unsigned_to_nat(1u);
v___x_6653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6653_, 0, v___x_6647_);
lean_ctor_set(v___x_6653_, 1, v___x_6611_);
lean_ctor_set(v___x_6653_, 2, v___x_6652_);
if (v_isShared_6552_ == 0)
{
lean_ctor_set(v___x_6551_, 1, v___x_6653_);
lean_ctor_set(v___x_6551_, 0, v___x_6651_);
v___x_6655_ = v___x_6551_;
goto v_reusejp_6654_;
}
else
{
lean_object* v_reuseFailAlloc_6707_; 
v_reuseFailAlloc_6707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6707_, 0, v___x_6651_);
lean_ctor_set(v_reuseFailAlloc_6707_, 1, v___x_6653_);
v___x_6655_ = v_reuseFailAlloc_6707_;
goto v_reusejp_6654_;
}
v_reusejp_6654_:
{
lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; 
v___x_6656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6656_, 0, v___x_6648_);
lean_ctor_set(v___x_6656_, 1, v___x_6655_);
v___x_6657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6657_, 0, v___x_6648_);
lean_ctor_set(v___x_6657_, 1, v___x_6656_);
v___x_6658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6658_, 0, v___x_6651_);
lean_ctor_set(v___x_6658_, 1, v___x_6657_);
lean_inc(v_mvarId_6639_);
v___x_6659_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6518_, v_a_6534_, v_goal_6512_, v___x_6611_, v_snd_6549_, v_mvarId_6639_, v_stopAtFirstFailure_6519_, v_goalStack_6640_, v___x_6650_, v___x_6658_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
lean_dec(v___x_6650_);
lean_dec_ref(v_goalStack_6640_);
lean_dec(v___x_6611_);
if (lean_obj_tag(v___x_6659_) == 0)
{
lean_object* v_a_6660_; lean_object* v___x_6662_; uint8_t v_isShared_6663_; uint8_t v_isSharedCheck_6698_; 
v_a_6660_ = lean_ctor_get(v___x_6659_, 0);
v_isSharedCheck_6698_ = !lean_is_exclusive(v___x_6659_);
if (v_isSharedCheck_6698_ == 0)
{
v___x_6662_ = v___x_6659_;
v_isShared_6663_ = v_isSharedCheck_6698_;
goto v_resetjp_6661_;
}
else
{
lean_inc(v_a_6660_);
lean_dec(v___x_6659_);
v___x_6662_ = lean_box(0);
v_isShared_6663_ = v_isSharedCheck_6698_;
goto v_resetjp_6661_;
}
v_resetjp_6661_:
{
lean_object* v_fst_6664_; 
v_fst_6664_ = lean_ctor_get(v_a_6660_, 0);
if (lean_obj_tag(v_fst_6664_) == 0)
{
lean_object* v_snd_6665_; lean_object* v_snd_6666_; lean_object* v_fst_6667_; lean_object* v_fst_6668_; lean_object* v___x_6669_; 
lean_del_object(v___x_6662_);
v_snd_6665_ = lean_ctor_get(v_a_6660_, 1);
lean_inc(v_snd_6665_);
lean_dec(v_a_6660_);
v_snd_6666_ = lean_ctor_get(v_snd_6665_, 1);
lean_inc(v_snd_6666_);
v_fst_6667_ = lean_ctor_get(v_snd_6665_, 0);
lean_inc(v_fst_6667_);
lean_dec(v_snd_6665_);
v_fst_6668_ = lean_ctor_get(v_snd_6666_, 0);
lean_inc(v_fst_6668_);
lean_dec(v_snd_6666_);
lean_inc(v_mvarId_6639_);
v___x_6669_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6639_, v___f_6610_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
if (lean_obj_tag(v___x_6669_) == 0)
{
lean_object* v_a_6670_; lean_object* v___x_6671_; 
v_a_6670_ = lean_ctor_get(v___x_6669_, 0);
lean_inc(v_a_6670_);
lean_dec_ref_known(v___x_6669_, 1);
lean_inc(v_mvarId_6639_);
v___x_6671_ = l_Lean_MVarId_getType(v_mvarId_6639_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
if (lean_obj_tag(v___x_6671_) == 0)
{
lean_object* v_a_6672_; uint8_t v___x_6673_; 
v_a_6672_ = lean_ctor_get(v___x_6671_, 0);
lean_inc(v_a_6672_);
lean_dec_ref_known(v___x_6671_, 1);
v___x_6673_ = l_Lean_Expr_isFalse(v_a_6672_);
lean_dec(v_a_6672_);
if (v___x_6673_ == 0)
{
lean_object* v___x_6674_; 
v___x_6674_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6639_, v_a_6670_, v___y_6526_);
lean_dec_ref(v___x_6674_);
v___y_6559_ = v_fst_6668_;
v___y_6560_ = v_fst_6667_;
v___y_6561_ = v___x_6647_;
v___y_6562_ = v___y_6527_;
v___y_6563_ = v___y_6528_;
goto v___jp_6558_;
}
else
{
lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; 
v___x_6675_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_6676_ = l_Lean_Meta_mkExpectedPropHint(v_a_6670_, v___x_6675_);
v___x_6677_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6639_, v___x_6676_, v___y_6526_);
lean_dec_ref(v___x_6677_);
v___y_6559_ = v_fst_6668_;
v___y_6560_ = v_fst_6667_;
v___y_6561_ = v___x_6647_;
v___y_6562_ = v___y_6527_;
v___y_6563_ = v___y_6528_;
goto v___jp_6558_;
}
}
else
{
lean_object* v_a_6678_; lean_object* v___x_6680_; uint8_t v_isShared_6681_; uint8_t v_isSharedCheck_6685_; 
lean_dec(v_a_6670_);
lean_dec(v_fst_6668_);
lean_dec(v_fst_6667_);
lean_dec(v_mvarId_6639_);
lean_dec(v_snd_6554_);
lean_del_object(v___x_6546_);
v_a_6678_ = lean_ctor_get(v___x_6671_, 0);
v_isSharedCheck_6685_ = !lean_is_exclusive(v___x_6671_);
if (v_isSharedCheck_6685_ == 0)
{
v___x_6680_ = v___x_6671_;
v_isShared_6681_ = v_isSharedCheck_6685_;
goto v_resetjp_6679_;
}
else
{
lean_inc(v_a_6678_);
lean_dec(v___x_6671_);
v___x_6680_ = lean_box(0);
v_isShared_6681_ = v_isSharedCheck_6685_;
goto v_resetjp_6679_;
}
v_resetjp_6679_:
{
lean_object* v___x_6683_; 
if (v_isShared_6681_ == 0)
{
v___x_6683_ = v___x_6680_;
goto v_reusejp_6682_;
}
else
{
lean_object* v_reuseFailAlloc_6684_; 
v_reuseFailAlloc_6684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6684_, 0, v_a_6678_);
v___x_6683_ = v_reuseFailAlloc_6684_;
goto v_reusejp_6682_;
}
v_reusejp_6682_:
{
return v___x_6683_;
}
}
}
}
else
{
lean_object* v_a_6686_; lean_object* v___x_6688_; uint8_t v_isShared_6689_; uint8_t v_isSharedCheck_6693_; 
lean_dec(v_fst_6668_);
lean_dec(v_fst_6667_);
lean_dec(v_mvarId_6639_);
lean_dec(v_snd_6554_);
lean_del_object(v___x_6546_);
v_a_6686_ = lean_ctor_get(v___x_6669_, 0);
v_isSharedCheck_6693_ = !lean_is_exclusive(v___x_6669_);
if (v_isSharedCheck_6693_ == 0)
{
v___x_6688_ = v___x_6669_;
v_isShared_6689_ = v_isSharedCheck_6693_;
goto v_resetjp_6687_;
}
else
{
lean_inc(v_a_6686_);
lean_dec(v___x_6669_);
v___x_6688_ = lean_box(0);
v_isShared_6689_ = v_isSharedCheck_6693_;
goto v_resetjp_6687_;
}
v_resetjp_6687_:
{
lean_object* v___x_6691_; 
if (v_isShared_6689_ == 0)
{
v___x_6691_ = v___x_6688_;
goto v_reusejp_6690_;
}
else
{
lean_object* v_reuseFailAlloc_6692_; 
v_reuseFailAlloc_6692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6692_, 0, v_a_6686_);
v___x_6691_ = v_reuseFailAlloc_6692_;
goto v_reusejp_6690_;
}
v_reusejp_6690_:
{
return v___x_6691_;
}
}
}
}
else
{
lean_object* v_val_6694_; lean_object* v___x_6696_; 
lean_inc_ref(v_fst_6664_);
lean_dec(v_a_6660_);
lean_dec(v_mvarId_6639_);
lean_dec_ref(v___f_6610_);
lean_dec(v_snd_6554_);
lean_del_object(v___x_6546_);
v_val_6694_ = lean_ctor_get(v_fst_6664_, 0);
lean_inc(v_val_6694_);
lean_dec_ref_known(v_fst_6664_, 1);
if (v_isShared_6663_ == 0)
{
lean_ctor_set(v___x_6662_, 0, v_val_6694_);
v___x_6696_ = v___x_6662_;
goto v_reusejp_6695_;
}
else
{
lean_object* v_reuseFailAlloc_6697_; 
v_reuseFailAlloc_6697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_val_6694_);
v___x_6696_ = v_reuseFailAlloc_6697_;
goto v_reusejp_6695_;
}
v_reusejp_6695_:
{
return v___x_6696_;
}
}
}
}
else
{
lean_object* v_a_6699_; lean_object* v___x_6701_; uint8_t v_isShared_6702_; uint8_t v_isSharedCheck_6706_; 
lean_dec(v_mvarId_6639_);
lean_dec_ref(v___f_6610_);
lean_dec(v_snd_6554_);
lean_del_object(v___x_6546_);
v_a_6699_ = lean_ctor_get(v___x_6659_, 0);
v_isSharedCheck_6706_ = !lean_is_exclusive(v___x_6659_);
if (v_isSharedCheck_6706_ == 0)
{
v___x_6701_ = v___x_6659_;
v_isShared_6702_ = v_isSharedCheck_6706_;
goto v_resetjp_6700_;
}
else
{
lean_inc(v_a_6699_);
lean_dec(v___x_6659_);
v___x_6701_ = lean_box(0);
v_isShared_6702_ = v_isSharedCheck_6706_;
goto v_resetjp_6700_;
}
v_resetjp_6700_:
{
lean_object* v___x_6704_; 
if (v_isShared_6702_ == 0)
{
v___x_6704_ = v___x_6701_;
goto v_reusejp_6703_;
}
else
{
lean_object* v_reuseFailAlloc_6705_; 
v_reuseFailAlloc_6705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6705_, 0, v_a_6699_);
v___x_6704_ = v_reuseFailAlloc_6705_;
goto v_reusejp_6703_;
}
v_reusejp_6703_:
{
return v___x_6704_;
}
}
}
}
}
else
{
lean_object* v_a_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6715_; 
lean_dec_ref(v___x_6643_);
lean_dec_ref(v_goalStack_6640_);
lean_dec(v_mvarId_6639_);
lean_dec(v___x_6611_);
lean_dec_ref(v___f_6610_);
lean_dec(v_snd_6554_);
lean_dec(v_fst_6553_);
lean_del_object(v___x_6551_);
lean_dec(v_snd_6549_);
lean_del_object(v___x_6546_);
lean_dec_ref(v___x_6538_);
lean_dec(v_a_6534_);
lean_dec_ref(v_kp_6518_);
lean_dec_ref(v_c_6513_);
lean_dec_ref(v_goal_6512_);
v_a_6708_ = lean_ctor_get(v___x_6645_, 0);
v_isSharedCheck_6715_ = !lean_is_exclusive(v___x_6645_);
if (v_isSharedCheck_6715_ == 0)
{
v___x_6710_ = v___x_6645_;
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_a_6708_);
lean_dec(v___x_6645_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6713_; 
if (v_isShared_6711_ == 0)
{
v___x_6713_ = v___x_6710_;
goto v_reusejp_6712_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
v___x_6713_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6712_;
}
v_reusejp_6712_:
{
return v___x_6713_;
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
lean_object* v_a_6724_; lean_object* v___x_6726_; uint8_t v_isShared_6727_; uint8_t v_isSharedCheck_6731_; 
lean_dec_ref(v___x_6538_);
lean_dec(v_a_6536_);
lean_dec(v_a_6534_);
lean_dec_ref(v_kp_6518_);
lean_dec_ref(v_c_6513_);
lean_dec_ref(v_goal_6512_);
v_a_6724_ = lean_ctor_get(v___x_6543_, 0);
v_isSharedCheck_6731_ = !lean_is_exclusive(v___x_6543_);
if (v_isSharedCheck_6731_ == 0)
{
v___x_6726_ = v___x_6543_;
v_isShared_6727_ = v_isSharedCheck_6731_;
goto v_resetjp_6725_;
}
else
{
lean_inc(v_a_6724_);
lean_dec(v___x_6543_);
v___x_6726_ = lean_box(0);
v_isShared_6727_ = v_isSharedCheck_6731_;
goto v_resetjp_6725_;
}
v_resetjp_6725_:
{
lean_object* v___x_6729_; 
if (v_isShared_6727_ == 0)
{
v___x_6729_ = v___x_6726_;
goto v_reusejp_6728_;
}
else
{
lean_object* v_reuseFailAlloc_6730_; 
v_reuseFailAlloc_6730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6730_, 0, v_a_6724_);
v___x_6729_ = v_reuseFailAlloc_6730_;
goto v_reusejp_6728_;
}
v_reusejp_6728_:
{
return v___x_6729_;
}
}
}
}
else
{
lean_object* v_a_6732_; lean_object* v___x_6734_; uint8_t v_isShared_6735_; uint8_t v_isSharedCheck_6739_; 
lean_dec(v_a_6534_);
lean_dec_ref(v_kp_6518_);
lean_dec(v_candidates_x3f_6516_);
lean_dec(v_numCases_6514_);
lean_dec_ref(v_c_6513_);
lean_dec_ref(v_goal_6512_);
v_a_6732_ = lean_ctor_get(v___x_6535_, 0);
v_isSharedCheck_6739_ = !lean_is_exclusive(v___x_6535_);
if (v_isSharedCheck_6739_ == 0)
{
v___x_6734_ = v___x_6535_;
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
else
{
lean_inc(v_a_6732_);
lean_dec(v___x_6535_);
v___x_6734_ = lean_box(0);
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
v_resetjp_6733_:
{
lean_object* v___x_6737_; 
if (v_isShared_6735_ == 0)
{
v___x_6737_ = v___x_6734_;
goto v_reusejp_6736_;
}
else
{
lean_object* v_reuseFailAlloc_6738_; 
v_reuseFailAlloc_6738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_a_6732_);
v___x_6737_ = v_reuseFailAlloc_6738_;
goto v_reusejp_6736_;
}
v_reusejp_6736_:
{
return v___x_6737_;
}
}
}
}
else
{
lean_object* v_a_6740_; lean_object* v___x_6742_; uint8_t v_isShared_6743_; uint8_t v_isSharedCheck_6747_; 
lean_dec_ref(v_kp_6518_);
lean_dec(v_candidates_x3f_6516_);
lean_dec(v_numCases_6514_);
lean_dec_ref(v_c_6513_);
lean_dec_ref(v_goal_6512_);
v_a_6740_ = lean_ctor_get(v___x_6533_, 0);
v_isSharedCheck_6747_ = !lean_is_exclusive(v___x_6533_);
if (v_isSharedCheck_6747_ == 0)
{
v___x_6742_ = v___x_6533_;
v_isShared_6743_ = v_isSharedCheck_6747_;
goto v_resetjp_6741_;
}
else
{
lean_inc(v_a_6740_);
lean_dec(v___x_6533_);
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
else
{
lean_object* v_a_6748_; lean_object* v___x_6750_; uint8_t v_isShared_6751_; uint8_t v_isSharedCheck_6755_; 
lean_dec_ref(v_kp_6518_);
lean_dec(v_candidates_x3f_6516_);
lean_dec(v_numCases_6514_);
lean_dec_ref(v_c_6513_);
lean_dec_ref(v_goal_6512_);
v_a_6748_ = lean_ctor_get(v___x_6530_, 0);
v_isSharedCheck_6755_ = !lean_is_exclusive(v___x_6530_);
if (v_isSharedCheck_6755_ == 0)
{
v___x_6750_ = v___x_6530_;
v_isShared_6751_ = v_isSharedCheck_6755_;
goto v_resetjp_6749_;
}
else
{
lean_inc(v_a_6748_);
lean_dec(v___x_6530_);
v___x_6750_ = lean_box(0);
v_isShared_6751_ = v_isSharedCheck_6755_;
goto v_resetjp_6749_;
}
v_resetjp_6749_:
{
lean_object* v___x_6753_; 
if (v_isShared_6751_ == 0)
{
v___x_6753_ = v___x_6750_;
goto v_reusejp_6752_;
}
else
{
lean_object* v_reuseFailAlloc_6754_; 
v_reuseFailAlloc_6754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6754_, 0, v_a_6748_);
v___x_6753_ = v_reuseFailAlloc_6754_;
goto v_reusejp_6752_;
}
v_reusejp_6752_:
{
return v___x_6753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_goal_6756_ = _args[0];
lean_object* v_c_6757_ = _args[1];
lean_object* v_numCases_6758_ = _args[2];
lean_object* v_isRec_6759_ = _args[3];
lean_object* v_candidates_x3f_6760_ = _args[4];
lean_object* v_compress_6761_ = _args[5];
lean_object* v_kp_6762_ = _args[6];
lean_object* v_stopAtFirstFailure_6763_ = _args[7];
lean_object* v___y_6764_ = _args[8];
lean_object* v___y_6765_ = _args[9];
lean_object* v___y_6766_ = _args[10];
lean_object* v___y_6767_ = _args[11];
lean_object* v___y_6768_ = _args[12];
lean_object* v___y_6769_ = _args[13];
lean_object* v___y_6770_ = _args[14];
lean_object* v___y_6771_ = _args[15];
lean_object* v___y_6772_ = _args[16];
lean_object* v___y_6773_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6774_; uint8_t v_compress_boxed_6775_; uint8_t v_stopAtFirstFailure_boxed_6776_; lean_object* v_res_6777_; 
v_isRec_boxed_6774_ = lean_unbox(v_isRec_6759_);
v_compress_boxed_6775_ = lean_unbox(v_compress_6761_);
v_stopAtFirstFailure_boxed_6776_ = lean_unbox(v_stopAtFirstFailure_6763_);
v_res_6777_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(v_goal_6756_, v_c_6757_, v_numCases_6758_, v_isRec_boxed_6774_, v_candidates_x3f_6760_, v_compress_boxed_6775_, v_kp_6762_, v_stopAtFirstFailure_boxed_6776_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_);
lean_dec(v___y_6772_);
lean_dec_ref(v___y_6771_);
lean_dec(v___y_6770_);
lean_dec_ref(v___y_6769_);
lean_dec(v___y_6768_);
lean_dec_ref(v___y_6767_);
lean_dec(v___y_6766_);
lean_dec_ref(v___y_6765_);
lean_dec(v___y_6764_);
return v_res_6777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_6778_, lean_object* v_numCases_6779_, uint8_t v_isRec_6780_, uint8_t v_stopAtFirstFailure_6781_, uint8_t v_compress_6782_, lean_object* v_candidates_x3f_6783_, lean_object* v_goal_6784_, lean_object* v_kp_6785_, lean_object* v_a_6786_, lean_object* v_a_6787_, lean_object* v_a_6788_, lean_object* v_a_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_, lean_object* v_a_6792_, lean_object* v_a_6793_, lean_object* v_a_6794_){
_start:
{
lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; lean_object* v___f_6799_; lean_object* v___x_6800_; 
v___x_6796_ = lean_box(v_isRec_6780_);
v___x_6797_ = lean_box(v_compress_6782_);
v___x_6798_ = lean_box(v_stopAtFirstFailure_6781_);
lean_inc_ref(v_goal_6784_);
v___f_6799_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed), 18, 8);
lean_closure_set(v___f_6799_, 0, v_goal_6784_);
lean_closure_set(v___f_6799_, 1, v_c_6778_);
lean_closure_set(v___f_6799_, 2, v_numCases_6779_);
lean_closure_set(v___f_6799_, 3, v___x_6796_);
lean_closure_set(v___f_6799_, 4, v_candidates_x3f_6783_);
lean_closure_set(v___f_6799_, 5, v___x_6797_);
lean_closure_set(v___f_6799_, 6, v_kp_6785_);
lean_closure_set(v___f_6799_, 7, v___x_6798_);
v___x_6800_ = l_Lean_Meta_Grind_withHoistedDecls___redArg(v_goal_6784_, v___f_6799_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_, v_a_6794_);
return v___x_6800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6801_ = _args[0];
lean_object* v_numCases_6802_ = _args[1];
lean_object* v_isRec_6803_ = _args[2];
lean_object* v_stopAtFirstFailure_6804_ = _args[3];
lean_object* v_compress_6805_ = _args[4];
lean_object* v_candidates_x3f_6806_ = _args[5];
lean_object* v_goal_6807_ = _args[6];
lean_object* v_kp_6808_ = _args[7];
lean_object* v_a_6809_ = _args[8];
lean_object* v_a_6810_ = _args[9];
lean_object* v_a_6811_ = _args[10];
lean_object* v_a_6812_ = _args[11];
lean_object* v_a_6813_ = _args[12];
lean_object* v_a_6814_ = _args[13];
lean_object* v_a_6815_ = _args[14];
lean_object* v_a_6816_ = _args[15];
lean_object* v_a_6817_ = _args[16];
lean_object* v_a_6818_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6819_; uint8_t v_stopAtFirstFailure_boxed_6820_; uint8_t v_compress_boxed_6821_; lean_object* v_res_6822_; 
v_isRec_boxed_6819_ = lean_unbox(v_isRec_6803_);
v_stopAtFirstFailure_boxed_6820_ = lean_unbox(v_stopAtFirstFailure_6804_);
v_compress_boxed_6821_ = lean_unbox(v_compress_6805_);
v_res_6822_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6801_, v_numCases_6802_, v_isRec_boxed_6819_, v_stopAtFirstFailure_boxed_6820_, v_compress_boxed_6821_, v_candidates_x3f_6806_, v_goal_6807_, v_kp_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_, v_a_6816_, v_a_6817_);
lean_dec(v_a_6817_);
lean_dec_ref(v_a_6816_);
lean_dec(v_a_6815_);
lean_dec_ref(v_a_6814_);
lean_dec(v_a_6813_);
lean_dec_ref(v_a_6812_);
lean_dec(v_a_6811_);
lean_dec_ref(v_a_6810_);
lean_dec(v_a_6809_);
return v_res_6822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6823_, lean_object* v_numCases_6824_, uint8_t v_isRec_6825_, uint8_t v_stopAtFirstFailure_6826_, uint8_t v_compress_6827_, lean_object* v_candidates_x3f_6828_, lean_object* v_goal_6829_, lean_object* v_x_6830_, lean_object* v_kp_6831_, lean_object* v_a_6832_, lean_object* v_a_6833_, lean_object* v_a_6834_, lean_object* v_a_6835_, lean_object* v_a_6836_, lean_object* v_a_6837_, lean_object* v_a_6838_, lean_object* v_a_6839_, lean_object* v_a_6840_){
_start:
{
lean_object* v___x_6842_; 
v___x_6842_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6823_, v_numCases_6824_, v_isRec_6825_, v_stopAtFirstFailure_6826_, v_compress_6827_, v_candidates_x3f_6828_, v_goal_6829_, v_kp_6831_, v_a_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_, v_a_6839_, v_a_6840_);
return v___x_6842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6843_ = _args[0];
lean_object* v_numCases_6844_ = _args[1];
lean_object* v_isRec_6845_ = _args[2];
lean_object* v_stopAtFirstFailure_6846_ = _args[3];
lean_object* v_compress_6847_ = _args[4];
lean_object* v_candidates_x3f_6848_ = _args[5];
lean_object* v_goal_6849_ = _args[6];
lean_object* v_x_6850_ = _args[7];
lean_object* v_kp_6851_ = _args[8];
lean_object* v_a_6852_ = _args[9];
lean_object* v_a_6853_ = _args[10];
lean_object* v_a_6854_ = _args[11];
lean_object* v_a_6855_ = _args[12];
lean_object* v_a_6856_ = _args[13];
lean_object* v_a_6857_ = _args[14];
lean_object* v_a_6858_ = _args[15];
lean_object* v_a_6859_ = _args[16];
lean_object* v_a_6860_ = _args[17];
lean_object* v_a_6861_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6862_; uint8_t v_stopAtFirstFailure_boxed_6863_; uint8_t v_compress_boxed_6864_; lean_object* v_res_6865_; 
v_isRec_boxed_6862_ = lean_unbox(v_isRec_6845_);
v_stopAtFirstFailure_boxed_6863_ = lean_unbox(v_stopAtFirstFailure_6846_);
v_compress_boxed_6864_ = lean_unbox(v_compress_6847_);
v_res_6865_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6843_, v_numCases_6844_, v_isRec_boxed_6862_, v_stopAtFirstFailure_boxed_6863_, v_compress_boxed_6864_, v_candidates_x3f_6848_, v_goal_6849_, v_x_6850_, v_kp_6851_, v_a_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_, v_a_6857_, v_a_6858_, v_a_6859_, v_a_6860_);
lean_dec(v_a_6860_);
lean_dec_ref(v_a_6859_);
lean_dec(v_a_6858_);
lean_dec_ref(v_a_6857_);
lean_dec(v_a_6856_);
lean_dec_ref(v_a_6855_);
lean_dec(v_a_6854_);
lean_dec_ref(v_a_6853_);
lean_dec(v_a_6852_);
lean_dec_ref(v_x_6850_);
return v_res_6865_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_6866_, lean_object* v_a_6867_, lean_object* v_goal_6868_, lean_object* v___x_6869_, lean_object* v_snd_6870_, lean_object* v___x_6871_, uint8_t v_stopAtFirstFailure_6872_, lean_object* v___x_6873_, lean_object* v_as_6874_, lean_object* v_as_x27_6875_, lean_object* v_b_6876_, lean_object* v_a_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_, lean_object* v___y_6884_, lean_object* v___y_6885_, lean_object* v___y_6886_){
_start:
{
lean_object* v___x_6888_; 
v___x_6888_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6866_, v_a_6867_, v_goal_6868_, v___x_6869_, v_snd_6870_, v___x_6871_, v_stopAtFirstFailure_6872_, v___x_6873_, v_as_x27_6875_, v_b_6876_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_, v___y_6886_);
return v___x_6888_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6889_ = _args[0];
lean_object* v_a_6890_ = _args[1];
lean_object* v_goal_6891_ = _args[2];
lean_object* v___x_6892_ = _args[3];
lean_object* v_snd_6893_ = _args[4];
lean_object* v___x_6894_ = _args[5];
lean_object* v_stopAtFirstFailure_6895_ = _args[6];
lean_object* v___x_6896_ = _args[7];
lean_object* v_as_6897_ = _args[8];
lean_object* v_as_x27_6898_ = _args[9];
lean_object* v_b_6899_ = _args[10];
lean_object* v_a_6900_ = _args[11];
lean_object* v___y_6901_ = _args[12];
lean_object* v___y_6902_ = _args[13];
lean_object* v___y_6903_ = _args[14];
lean_object* v___y_6904_ = _args[15];
lean_object* v___y_6905_ = _args[16];
lean_object* v___y_6906_ = _args[17];
lean_object* v___y_6907_ = _args[18];
lean_object* v___y_6908_ = _args[19];
lean_object* v___y_6909_ = _args[20];
lean_object* v___y_6910_ = _args[21];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6911_; lean_object* v_res_6912_; 
v_stopAtFirstFailure_boxed_6911_ = lean_unbox(v_stopAtFirstFailure_6895_);
v_res_6912_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6889_, v_a_6890_, v_goal_6891_, v___x_6892_, v_snd_6893_, v___x_6894_, v_stopAtFirstFailure_boxed_6911_, v___x_6896_, v_as_6897_, v_as_x27_6898_, v_b_6899_, v_a_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_);
lean_dec(v___y_6909_);
lean_dec_ref(v___y_6908_);
lean_dec(v___y_6907_);
lean_dec_ref(v___y_6906_);
lean_dec(v___y_6905_);
lean_dec_ref(v___y_6904_);
lean_dec(v___y_6903_);
lean_dec_ref(v___y_6902_);
lean_dec(v___y_6901_);
lean_dec(v_as_x27_6898_);
lean_dec(v_as_6897_);
lean_dec_ref(v___x_6896_);
lean_dec(v___x_6892_);
return v_res_6912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_mvarId_6913_, lean_object* v_val_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_){
_start:
{
lean_object* v___x_6925_; 
v___x_6925_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6913_, v_val_6914_, v___y_6921_);
return v___x_6925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_mvarId_6926_, lean_object* v_val_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_, lean_object* v___y_6936_, lean_object* v___y_6937_){
_start:
{
lean_object* v_res_6938_; 
v_res_6938_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_mvarId_6926_, v_val_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_, v___y_6934_, v___y_6935_, v___y_6936_);
lean_dec(v___y_6936_);
lean_dec_ref(v___y_6935_);
lean_dec(v___y_6934_);
lean_dec_ref(v___y_6933_);
lean_dec(v___y_6932_);
lean_dec_ref(v___y_6931_);
lean_dec(v___y_6930_);
lean_dec_ref(v___y_6929_);
lean_dec(v___y_6928_);
return v_res_6938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4(lean_object* v_00_u03b2_6939_, lean_object* v_x_6940_, lean_object* v_x_6941_, lean_object* v_x_6942_){
_start:
{
lean_object* v___x_6943_; 
v___x_6943_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_x_6940_, v_x_6941_, v_x_6942_);
return v___x_6943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(lean_object* v_00_u03b2_6944_, lean_object* v_x_6945_, size_t v_x_6946_, size_t v_x_6947_, lean_object* v_x_6948_, lean_object* v_x_6949_){
_start:
{
lean_object* v___x_6950_; 
v___x_6950_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6945_, v_x_6946_, v_x_6947_, v_x_6948_, v_x_6949_);
return v___x_6950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b2_6951_, lean_object* v_x_6952_, lean_object* v_x_6953_, lean_object* v_x_6954_, lean_object* v_x_6955_, lean_object* v_x_6956_){
_start:
{
size_t v_x_118974__boxed_6957_; size_t v_x_118975__boxed_6958_; lean_object* v_res_6959_; 
v_x_118974__boxed_6957_ = lean_unbox_usize(v_x_6953_);
lean_dec(v_x_6953_);
v_x_118975__boxed_6958_ = lean_unbox_usize(v_x_6954_);
lean_dec(v_x_6954_);
v_res_6959_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(v_00_u03b2_6951_, v_x_6952_, v_x_118974__boxed_6957_, v_x_118975__boxed_6958_, v_x_6955_, v_x_6956_);
return v_res_6959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_6960_, lean_object* v_n_6961_, lean_object* v_k_6962_, lean_object* v_v_6963_){
_start:
{
lean_object* v___x_6964_; 
v___x_6964_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v_n_6961_, v_k_6962_, v_v_6963_);
return v___x_6964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_6965_, size_t v_depth_6966_, lean_object* v_keys_6967_, lean_object* v_vals_6968_, lean_object* v_heq_6969_, lean_object* v_i_6970_, lean_object* v_entries_6971_){
_start:
{
lean_object* v___x_6972_; 
v___x_6972_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_6966_, v_keys_6967_, v_vals_6968_, v_i_6970_, v_entries_6971_);
return v___x_6972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_6973_, lean_object* v_depth_6974_, lean_object* v_keys_6975_, lean_object* v_vals_6976_, lean_object* v_heq_6977_, lean_object* v_i_6978_, lean_object* v_entries_6979_){
_start:
{
size_t v_depth_boxed_6980_; lean_object* v_res_6981_; 
v_depth_boxed_6980_ = lean_unbox_usize(v_depth_6974_);
lean_dec(v_depth_6974_);
v_res_6981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(v_00_u03b2_6973_, v_depth_boxed_6980_, v_keys_6975_, v_vals_6976_, v_heq_6977_, v_i_6978_, v_entries_6979_);
lean_dec_ref(v_vals_6976_);
lean_dec_ref(v_keys_6975_);
return v_res_6981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6982_, lean_object* v_x_6983_, lean_object* v_x_6984_, lean_object* v_x_6985_, lean_object* v_x_6986_){
_start:
{
lean_object* v___x_6987_; 
v___x_6987_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_x_6983_, v_x_6984_, v_x_6985_, v_x_6986_);
return v___x_6987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_){
_start:
{
lean_object* v___x_7001_; 
v___x_7001_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6988_, v___y_6990_, v___y_6991_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_);
return v___x_7001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_){
_start:
{
lean_object* v_res_7015_; 
v_res_7015_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_);
lean_dec(v___y_7013_);
lean_dec_ref(v___y_7012_);
lean_dec(v___y_7011_);
lean_dec_ref(v___y_7010_);
lean_dec(v___y_7009_);
lean_dec_ref(v___y_7008_);
lean_dec(v___y_7007_);
lean_dec_ref(v___y_7006_);
lean_dec(v___y_7005_);
lean_dec_ref(v___y_7003_);
return v_res_7015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_){
_start:
{
lean_object* v___x_7027_; lean_object* v___x_7028_; 
v___x_7027_ = lean_st_mk_ref(v_goal_7016_);
v___x_7028_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_7027_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_);
if (lean_obj_tag(v___x_7028_) == 0)
{
lean_object* v_a_7029_; lean_object* v___x_7031_; uint8_t v_isShared_7032_; uint8_t v_isSharedCheck_7038_; 
v_a_7029_ = lean_ctor_get(v___x_7028_, 0);
v_isSharedCheck_7038_ = !lean_is_exclusive(v___x_7028_);
if (v_isSharedCheck_7038_ == 0)
{
v___x_7031_ = v___x_7028_;
v_isShared_7032_ = v_isSharedCheck_7038_;
goto v_resetjp_7030_;
}
else
{
lean_inc(v_a_7029_);
lean_dec(v___x_7028_);
v___x_7031_ = lean_box(0);
v_isShared_7032_ = v_isSharedCheck_7038_;
goto v_resetjp_7030_;
}
v_resetjp_7030_:
{
lean_object* v___x_7033_; lean_object* v___x_7034_; lean_object* v___x_7036_; 
v___x_7033_ = lean_st_ref_get(v___x_7027_);
lean_dec(v___x_7027_);
v___x_7034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7034_, 0, v_a_7029_);
lean_ctor_set(v___x_7034_, 1, v___x_7033_);
if (v_isShared_7032_ == 0)
{
lean_ctor_set(v___x_7031_, 0, v___x_7034_);
v___x_7036_ = v___x_7031_;
goto v_reusejp_7035_;
}
else
{
lean_object* v_reuseFailAlloc_7037_; 
v_reuseFailAlloc_7037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7037_, 0, v___x_7034_);
v___x_7036_ = v_reuseFailAlloc_7037_;
goto v_reusejp_7035_;
}
v_reusejp_7035_:
{
return v___x_7036_;
}
}
}
else
{
lean_object* v_a_7039_; lean_object* v___x_7041_; uint8_t v_isShared_7042_; uint8_t v_isSharedCheck_7046_; 
lean_dec(v___x_7027_);
v_a_7039_ = lean_ctor_get(v___x_7028_, 0);
v_isSharedCheck_7046_ = !lean_is_exclusive(v___x_7028_);
if (v_isSharedCheck_7046_ == 0)
{
v___x_7041_ = v___x_7028_;
v_isShared_7042_ = v_isSharedCheck_7046_;
goto v_resetjp_7040_;
}
else
{
lean_inc(v_a_7039_);
lean_dec(v___x_7028_);
v___x_7041_ = lean_box(0);
v_isShared_7042_ = v_isSharedCheck_7046_;
goto v_resetjp_7040_;
}
v_resetjp_7040_:
{
lean_object* v___x_7044_; 
if (v_isShared_7042_ == 0)
{
v___x_7044_ = v___x_7041_;
goto v_reusejp_7043_;
}
else
{
lean_object* v_reuseFailAlloc_7045_; 
v_reuseFailAlloc_7045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7045_, 0, v_a_7039_);
v___x_7044_ = v_reuseFailAlloc_7045_;
goto v_reusejp_7043_;
}
v_reusejp_7043_:
{
return v___x_7044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_){
_start:
{
lean_object* v_res_7058_; 
v_res_7058_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_7047_, v___y_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
lean_dec(v___y_7056_);
lean_dec_ref(v___y_7055_);
lean_dec(v___y_7054_);
lean_dec_ref(v___y_7053_);
lean_dec(v___y_7052_);
lean_dec_ref(v___y_7051_);
lean_dec(v___y_7050_);
lean_dec_ref(v___y_7049_);
lean_dec(v___y_7048_);
return v_res_7058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_7059_, lean_object* v___f_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_, lean_object* v___y_7065_, lean_object* v___y_7066_, lean_object* v___y_7067_, lean_object* v___y_7068_, lean_object* v___y_7069_, lean_object* v___y_7070_, lean_object* v___y_7071_, lean_object* v___y_7072_){
_start:
{
lean_object* v___x_7074_; lean_object* v___x_7075_; 
v___x_7074_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_7074_, 0, v___y_7059_);
v___x_7075_ = l_Lean_Meta_Grind_Action_andThen(v___x_7074_, v___f_7060_, v___y_7061_, v___y_7062_, v___y_7063_, v___y_7064_, v___y_7065_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_, v___y_7070_, v___y_7071_, v___y_7072_);
return v___x_7075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_7076_, lean_object* v___f_7077_, lean_object* v___y_7078_, lean_object* v___y_7079_, lean_object* v___y_7080_, lean_object* v___y_7081_, lean_object* v___y_7082_, lean_object* v___y_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_){
_start:
{
lean_object* v_res_7091_; 
v_res_7091_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_7076_, v___f_7077_, v___y_7078_, v___y_7079_, v___y_7080_, v___y_7081_, v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_, v___y_7088_, v___y_7089_);
lean_dec(v___y_7089_);
lean_dec_ref(v___y_7088_);
lean_dec(v___y_7087_);
lean_dec_ref(v___y_7086_);
lean_dec(v___y_7085_);
lean_dec_ref(v___y_7084_);
lean_dec(v___y_7083_);
lean_dec_ref(v___y_7082_);
lean_dec(v___y_7081_);
return v_res_7091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_7093_, uint8_t v_compress_7094_, lean_object* v_goal_7095_, lean_object* v_kna_7096_, lean_object* v_kp_7097_, lean_object* v_a_7098_, lean_object* v_a_7099_, lean_object* v_a_7100_, lean_object* v_a_7101_, lean_object* v_a_7102_, lean_object* v_a_7103_, lean_object* v_a_7104_, lean_object* v_a_7105_, lean_object* v_a_7106_){
_start:
{
lean_object* v_toGoalState_7108_; lean_object* v_split_7109_; lean_object* v_mvarId_7110_; lean_object* v_candidates_7111_; lean_object* v___f_7112_; lean_object* v___f_7113_; lean_object* v___x_7114_; 
v_toGoalState_7108_ = lean_ctor_get(v_goal_7095_, 0);
v_split_7109_ = lean_ctor_get(v_toGoalState_7108_, 15);
v_mvarId_7110_ = lean_ctor_get(v_goal_7095_, 1);
lean_inc(v_mvarId_7110_);
v_candidates_7111_ = lean_ctor_get(v_split_7109_, 0);
lean_inc(v_candidates_7111_);
v___f_7112_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_7113_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_7113_, 0, v_goal_7095_);
v___x_7114_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_7110_, v___f_7113_, v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_, v_a_7106_);
if (lean_obj_tag(v___x_7114_) == 0)
{
lean_object* v_a_7115_; lean_object* v_fst_7116_; 
v_a_7115_ = lean_ctor_get(v___x_7114_, 0);
lean_inc(v_a_7115_);
lean_dec_ref_known(v___x_7114_, 1);
v_fst_7116_ = lean_ctor_get(v_a_7115_, 0);
if (lean_obj_tag(v_fst_7116_) == 1)
{
lean_object* v_snd_7117_; lean_object* v_c_7118_; lean_object* v_numCases_7119_; uint8_t v_isRec_7120_; lean_object* v___y_7122_; lean_object* v___x_7130_; lean_object* v___x_7131_; lean_object* v___x_7132_; uint8_t v___x_7135_; 
lean_inc_ref(v_fst_7116_);
v_snd_7117_ = lean_ctor_get(v_a_7115_, 1);
lean_inc(v_snd_7117_);
lean_dec(v_a_7115_);
v_c_7118_ = lean_ctor_get(v_fst_7116_, 0);
lean_inc_ref(v_c_7118_);
v_numCases_7119_ = lean_ctor_get(v_fst_7116_, 1);
lean_inc(v_numCases_7119_);
v_isRec_7120_ = lean_ctor_get_uint8(v_fst_7116_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_7116_, 2);
v___x_7130_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_7118_);
v___x_7131_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_7117_, v___x_7130_);
lean_dec_ref(v___x_7130_);
v___x_7132_ = lean_unsigned_to_nat(1u);
v___x_7135_ = lean_nat_dec_lt(v___x_7132_, v_numCases_7119_);
if (v___x_7135_ == 0)
{
if (v_isRec_7120_ == 0)
{
v___y_7122_ = v___x_7131_;
goto v___jp_7121_;
}
else
{
goto v___jp_7133_;
}
}
else
{
goto v___jp_7133_;
}
v___jp_7121_:
{
lean_object* v___f_7123_; lean_object* v___x_7124_; lean_object* v___x_7125_; lean_object* v___x_7126_; lean_object* v___x_7127_; lean_object* v___x_7128_; lean_object* v___x_7129_; 
v___f_7123_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_7123_, 0, v___y_7122_);
lean_closure_set(v___f_7123_, 1, v___f_7112_);
v___x_7124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7124_, 0, v_candidates_7111_);
v___x_7125_ = lean_box(v_isRec_7120_);
v___x_7126_ = lean_box(v_stopAtFirstFailure_7093_);
v___x_7127_ = lean_box(v_compress_7094_);
v___x_7128_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_7128_, 0, v_c_7118_);
lean_closure_set(v___x_7128_, 1, v_numCases_7119_);
lean_closure_set(v___x_7128_, 2, v___x_7125_);
lean_closure_set(v___x_7128_, 3, v___x_7126_);
lean_closure_set(v___x_7128_, 4, v___x_7127_);
lean_closure_set(v___x_7128_, 5, v___x_7124_);
v___x_7129_ = l_Lean_Meta_Grind_Action_andThen(v___x_7128_, v___f_7123_, v_snd_7117_, v_kna_7096_, v_kp_7097_, v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_, v_a_7106_);
return v___x_7129_;
}
v___jp_7133_:
{
lean_object* v___x_7134_; 
v___x_7134_ = lean_nat_add(v___x_7131_, v___x_7132_);
lean_dec(v___x_7131_);
v___y_7122_ = v___x_7134_;
goto v___jp_7121_;
}
}
else
{
lean_object* v_snd_7136_; lean_object* v___x_7137_; 
lean_dec(v_candidates_7111_);
lean_dec_ref(v_kp_7097_);
v_snd_7136_ = lean_ctor_get(v_a_7115_, 1);
lean_inc(v_snd_7136_);
lean_dec(v_a_7115_);
lean_inc(v_a_7106_);
lean_inc_ref(v_a_7105_);
lean_inc(v_a_7104_);
lean_inc_ref(v_a_7103_);
lean_inc(v_a_7102_);
lean_inc_ref(v_a_7101_);
lean_inc(v_a_7100_);
lean_inc_ref(v_a_7099_);
lean_inc(v_a_7098_);
v___x_7137_ = lean_apply_11(v_kna_7096_, v_snd_7136_, v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_, v_a_7106_, lean_box(0));
return v___x_7137_;
}
}
else
{
lean_object* v_a_7138_; lean_object* v___x_7140_; uint8_t v_isShared_7141_; uint8_t v_isSharedCheck_7145_; 
lean_dec(v_candidates_7111_);
lean_dec_ref(v_kp_7097_);
lean_dec_ref(v_kna_7096_);
v_a_7138_ = lean_ctor_get(v___x_7114_, 0);
v_isSharedCheck_7145_ = !lean_is_exclusive(v___x_7114_);
if (v_isSharedCheck_7145_ == 0)
{
v___x_7140_ = v___x_7114_;
v_isShared_7141_ = v_isSharedCheck_7145_;
goto v_resetjp_7139_;
}
else
{
lean_inc(v_a_7138_);
lean_dec(v___x_7114_);
v___x_7140_ = lean_box(0);
v_isShared_7141_ = v_isSharedCheck_7145_;
goto v_resetjp_7139_;
}
v_resetjp_7139_:
{
lean_object* v___x_7143_; 
if (v_isShared_7141_ == 0)
{
v___x_7143_ = v___x_7140_;
goto v_reusejp_7142_;
}
else
{
lean_object* v_reuseFailAlloc_7144_; 
v_reuseFailAlloc_7144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
v___x_7143_ = v_reuseFailAlloc_7144_;
goto v_reusejp_7142_;
}
v_reusejp_7142_:
{
return v___x_7143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_7146_, lean_object* v_compress_7147_, lean_object* v_goal_7148_, lean_object* v_kna_7149_, lean_object* v_kp_7150_, lean_object* v_a_7151_, lean_object* v_a_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_, lean_object* v_a_7155_, lean_object* v_a_7156_, lean_object* v_a_7157_, lean_object* v_a_7158_, lean_object* v_a_7159_, lean_object* v_a_7160_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_7161_; uint8_t v_compress_boxed_7162_; lean_object* v_res_7163_; 
v_stopAtFirstFailure_boxed_7161_ = lean_unbox(v_stopAtFirstFailure_7146_);
v_compress_boxed_7162_ = lean_unbox(v_compress_7147_);
v_res_7163_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_7161_, v_compress_boxed_7162_, v_goal_7148_, v_kna_7149_, v_kp_7150_, v_a_7151_, v_a_7152_, v_a_7153_, v_a_7154_, v_a_7155_, v_a_7156_, v_a_7157_, v_a_7158_, v_a_7159_);
lean_dec(v_a_7159_);
lean_dec_ref(v_a_7158_);
lean_dec(v_a_7157_);
lean_dec_ref(v_a_7156_);
lean_dec(v_a_7155_);
lean_dec_ref(v_a_7154_);
lean_dec(v_a_7153_);
lean_dec_ref(v_a_7152_);
lean_dec(v_a_7151_);
return v_res_7163_;
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
