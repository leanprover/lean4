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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18_value;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "of_eq_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 180, 29, 33, 135, 171, 75, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "of_eq_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 242, 111, 233, 108, 43, 191, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "or_of_and_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_value),LEAN_SCALAR_PTR_LITERAL(64, 20, 245, 101, 69, 170, 96, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object* v_c_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object* v_c_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* v_c_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_195_, v_a_196_, v_a_200_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* v_c_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(v_c_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___x_1793_; 
lean_inc_ref(v_e_1532_);
v___x_1793_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1532_, v_a_1540_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1822_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1822_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1822_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = l_Lean_Expr_cleanupAnnotations(v_a_1794_);
lean_dec(v_a_1794_);
v___x_1799_ = l_Lean_Expr_isApp(v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1798_);
v___x_1801_ = l_Lean_Expr_isApp(v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v___x_1798_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
lean_object* v_arg_1802_; lean_object* v_arg_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_arg_1802_ = lean_ctor_get(v___x_1798_, 1);
lean_inc_ref(v_arg_1802_);
lean_dec_ref(v___x_1798_);
v_arg_1803_ = lean_ctor_get(v___x_1800_, 1);
lean_inc_ref(v_arg_1803_);
v___x_1804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1806_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1808_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1807_);
if (v___x_1808_ == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = l_Lean_Expr_isApp(v___x_1804_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_arg_1802_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1812_ = l_Lean_Expr_isConstOf(v___x_1810_, v___x_1811_);
lean_dec_ref(v___x_1810_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_arg_1802_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1532_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_arg_1802_);
lean_dec_ref(v_e_1532_);
v___x_1814_ = lean_unsigned_to_nat(2u);
v___x_1815_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*1, v___x_1813_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*1 + 1, v___x_1813_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1815_);
v___x_1817_ = v___x_1796_;
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
else
{
lean_object* v___x_1819_; 
lean_del_object(v___x_1796_);
v___x_1819_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1532_, v_arg_1803_, v_arg_1802_, v_a_1533_, v_a_1537_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1819_;
}
}
}
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v___x_1804_);
lean_del_object(v___x_1796_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1532_, v_arg_1803_, v_arg_1802_, v_a_1533_, v_a_1537_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v___x_1804_);
lean_del_object(v___x_1796_);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1532_, v_arg_1803_, v_arg_1802_, v_a_1533_, v_a_1537_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_e_1532_);
v_a_1823_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1793_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1793_);
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
v___jp_1544_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
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
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = l_Lean_Expr_getAppNumArgs(v_e_1532_);
v___x_1562_ = lean_nat_sub(v___x_1561_, v___x_1560_);
lean_dec(v___x_1561_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v___x_1560_);
lean_dec(v___x_1562_);
v___x_1564_ = l_Lean_Expr_getRevArg_x21(v_e_1532_, v___x_1563_);
lean_dec_ref(v_e_1532_);
v___x_1565_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1564_, v___y_1556_, v___y_1554_, v___y_1559_, v___y_1558_, v___y_1555_, v___y_1557_);
return v___x_1565_;
}
v___jp_1566_:
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Lean_Expr_isFVar(v_e_1532_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_e_1532_);
v___x_1579_ = lean_box(1);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc_ref(v_e_1532_);
v___x_1581_ = lean_infer_type(v_e_1532_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Meta_whnfD(v_a_1582_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_n(v_a_1584_, 2);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1586_ = l_Lean_MessageData_ofExpr(v_e_1532_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_indentExpr(v_a_1584_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_Expr_getAppFn(v_a_1584_);
lean_dec(v_a_1584_);
if (lean_obj_tag(v___x_1592_) == 4)
{
lean_object* v_declName_1593_; lean_object* v___x_1594_; 
v_declName_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_declName_1593_);
lean_dec_ref_known(v___x_1592_, 2);
v___x_1594_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1593_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1627_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1627_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1627_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
if (lean_obj_tag(v_a_1595_) == 5)
{
lean_object* v_val_1599_; lean_object* v_ctors_1600_; uint8_t v_isRec_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_dec_ref_known(v___x_1591_, 2);
v_val_1599_ = lean_ctor_get(v_a_1595_, 0);
lean_inc_ref(v_val_1599_);
lean_dec_ref_known(v_a_1595_, 1);
v_ctors_1600_ = lean_ctor_get(v_val_1599_, 4);
lean_inc(v_ctors_1600_);
v_isRec_1601_ = lean_ctor_get_uint8(v_val_1599_, sizeof(void*)*6);
lean_dec_ref(v_val_1599_);
v___x_1602_ = l_List_lengthTR___redArg(v_ctors_1600_);
lean_dec(v_ctors_1600_);
v___x_1603_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1, v_isRec_1601_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1 + 1, v___y_1567_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1603_);
v___x_1605_ = v___x_1597_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v___x_1607_; 
lean_del_object(v___x_1597_);
lean_dec(v_a_1595_);
v___x_1607_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1572_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; uint8_t v_verbose_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_verbose_1609_ = lean_ctor_get_uint8(v_a_1608_, 0);
lean_dec(v_a_1608_);
if (v_verbose_1609_ == 0)
{
lean_dec_ref_known(v___x_1591_, 2);
goto v___jp_1547_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_Sym_reportIssue(v___x_1591_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_dec_ref_known(v___x_1610_, 1);
goto v___jp_1547_;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref_known(v___x_1591_, 2);
v_a_1619_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1607_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1607_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref_known(v___x_1591_, 2);
v_a_1628_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1594_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1594_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v___x_1636_; 
lean_dec_ref(v___x_1592_);
v___x_1636_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1572_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; uint8_t v_verbose_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v_verbose_1638_ = lean_ctor_get_uint8(v_a_1637_, 0);
lean_dec(v_a_1637_);
if (v_verbose_1638_ == 0)
{
lean_dec_ref_known(v___x_1591_, 2);
goto v___jp_1550_;
}
else
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Sym_reportIssue(v___x_1591_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref_known(v___x_1639_, 1);
goto v___jp_1550_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref_known(v___x_1591_, 2);
v_a_1648_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1636_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1636_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_e_1532_);
v_a_1656_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1583_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1583_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v_e_1532_);
v_a_1664_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1581_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1581_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
v___jp_1672_:
{
uint8_t v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Grind_isIte(v_e_1532_);
if (v___x_1683_ == 0)
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_isDIte(v_e_1532_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1532_, v___y_1673_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; uint8_t v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = lean_unbox(v_a_1686_);
lean_dec(v_a_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_inc_ref(v_e_1532_);
v___x_1688_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1532_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1748_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1748_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1748_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_unbox(v_a_1689_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v_env_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_st_ref_get(v___y_1682_);
v_env_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc_ref(v_env_1695_);
lean_dec(v___x_1694_);
v___x_1696_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1695_, v_e_1532_);
if (lean_obj_tag(v___x_1696_) == 1)
{
lean_object* v_val_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1703_; 
lean_dec_ref(v_e_1532_);
v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1697_);
lean_dec(v_val_1697_);
v___x_1699_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
v___x_1700_ = lean_unbox(v_a_1689_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*1, v___x_1700_);
v___x_1701_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*1 + 1, v___x_1701_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1699_);
v___x_1703_ = v___x_1691_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1699_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; 
lean_dec(v___x_1696_);
lean_del_object(v___x_1691_);
v___x_1705_ = l_Lean_Expr_getAppFn(v_e_1532_);
if (lean_obj_tag(v___x_1705_) == 4)
{
lean_object* v_declName_1706_; lean_object* v___x_1707_; 
v_declName_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_declName_1706_);
lean_dec_ref_known(v___x_1705_, 2);
v___x_1707_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1706_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
if (lean_obj_tag(v_a_1708_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1710_; 
v_val_1709_ = lean_ctor_get(v_a_1708_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1708_, 1);
lean_inc_ref(v_e_1532_);
v___x_1710_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1532_, v___y_1673_, v___y_1677_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1725_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
if (v___x_1715_ == 0)
{
uint8_t v___x_1716_; 
lean_del_object(v___x_1713_);
lean_dec(v_val_1709_);
v___x_1716_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___y_1567_ = v___x_1716_;
v___y_1568_ = v___y_1673_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
goto v___jp_1566_;
}
else
{
lean_object* v_ctors_1717_; uint8_t v_isRec_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1723_; 
lean_dec_ref(v_e_1532_);
v_ctors_1717_ = lean_ctor_get(v_val_1709_, 4);
lean_inc(v_ctors_1717_);
v_isRec_1718_ = lean_ctor_get_uint8(v_val_1709_, sizeof(void*)*6);
lean_dec(v_val_1709_);
v___x_1719_ = l_List_lengthTR___redArg(v_ctors_1717_);
lean_dec(v_ctors_1717_);
v___x_1720_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*1, v_isRec_1718_);
v___x_1721_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*1 + 1, v___x_1721_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1720_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1720_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_val_1709_);
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1532_);
v_a_1726_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1710_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1710_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
uint8_t v___x_1734_; 
lean_dec(v_a_1708_);
v___x_1734_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___y_1567_ = v___x_1734_;
v___y_1568_ = v___y_1673_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
goto v___jp_1566_;
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1532_);
v_a_1735_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1707_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1707_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
uint8_t v___x_1743_; 
lean_dec_ref(v___x_1705_);
v___x_1743_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___y_1567_ = v___x_1743_;
v___y_1568_ = v___y_1673_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1532_);
v___x_1744_ = lean_box(0);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1744_);
v___x_1746_ = v___x_1691_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec_ref(v_e_1532_);
v_a_1749_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1688_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1688_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_toCold_1757_; lean_object* v_options_1758_; uint8_t v_hasTrace_1759_; 
v_toCold_1757_ = lean_ctor_get(v___y_1681_, 0);
v_options_1758_ = lean_ctor_get(v_toCold_1757_, 2);
v_hasTrace_1759_ = lean_ctor_get_uint8(v_options_1758_, sizeof(void*)*1);
if (v_hasTrace_1759_ == 0)
{
lean_dec_ref(v_e_1532_);
goto v___jp_1544_;
}
else
{
lean_object* v_inheritedTraceOptions_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_inheritedTraceOptions_1760_ = lean_ctor_get(v_toCold_1757_, 11);
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1760_, v_options_1758_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec_ref(v_e_1532_);
goto v___jp_1544_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_Grind_updateLastTag(v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1764_, 1);
v___x_1765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1766_ = l_Lean_MessageData_ofExpr(v_e_1532_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1761_, v___x_1767_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_dec_ref_known(v___x_1768_, 1);
goto v___jp_1544_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
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
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v_e_1532_);
v_a_1777_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1764_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1764_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v_e_1532_);
v_a_1785_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1685_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1685_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
v___y_1554_ = v___y_1677_;
v___y_1555_ = v___y_1681_;
v___y_1556_ = v___y_1673_;
v___y_1557_ = v___y_1682_;
v___y_1558_ = v___y_1680_;
v___y_1559_ = v___y_1679_;
goto v___jp_1553_;
}
}
else
{
v___y_1554_ = v___y_1677_;
v___y_1555_ = v___y_1681_;
v___y_1556_ = v___y_1673_;
v___y_1557_ = v___y_1682_;
v___y_1558_ = v___y_1680_;
v___y_1559_ = v___y_1679_;
goto v___jp_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec(v_a_1832_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1844_, lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1844_, v_msg_1845_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1858_, lean_object* v_msg_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1858_, v_msg_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec(v___y_1860_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1872_, lean_object* v_constName_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_constName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1886_, v_constName_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1900_, lean_object* v_ref_1901_, lean_object* v_constName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1901_, v_constName_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_ref_1916_, lean_object* v_constName_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1915_, v_ref_1916_, v_constName_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec(v_ref_1916_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1930_, lean_object* v_ref_1931_, lean_object* v_msg_1932_, lean_object* v_declHint_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1931_, v_msg_1932_, v_declHint_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_ref_1947_, lean_object* v_msg_1948_, lean_object* v_declHint_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1946_, v_ref_1947_, v_msg_1948_, v_declHint_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec(v_ref_1947_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1962_, lean_object* v_declHint_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1962_, v_declHint_1963_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1976_, lean_object* v_declHint_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1976_, v_declHint_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec(v___y_1978_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1990_, lean_object* v_ref_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1991_, v_msg_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_ref_2006_, lean_object* v_msg_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2005_, v_ref_2006_, v_msg_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v_ref_2006_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2020_, lean_object* v_msg_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2021_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2034_, lean_object* v_msg_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2034_, v_msg_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v___y_2036_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2048_, lean_object* v_x_2049_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_box(0);
return v___x_2050_;
}
else
{
lean_object* v_key_2051_; lean_object* v_value_2052_; lean_object* v_tail_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; uint8_t v___x_2058_; 
v_key_2051_ = lean_ctor_get(v_x_2049_, 0);
v_value_2052_ = lean_ctor_get(v_x_2049_, 1);
v_tail_2053_ = lean_ctor_get(v_x_2049_, 2);
v_fst_2054_ = lean_ctor_get(v_key_2051_, 0);
v_snd_2055_ = lean_ctor_get(v_key_2051_, 1);
v_fst_2056_ = lean_ctor_get(v_a_2048_, 0);
v_snd_2057_ = lean_ctor_get(v_a_2048_, 1);
v___x_2058_ = lean_expr_eqv(v_fst_2054_, v_fst_2056_);
if (v___x_2058_ == 0)
{
v_x_2049_ = v_tail_2053_;
goto _start;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_expr_eqv(v_snd_2055_, v_snd_2057_);
if (v___x_2060_ == 0)
{
v_x_2049_ = v_tail_2053_;
goto _start;
}
else
{
lean_object* v___x_2062_; 
lean_inc(v_value_2052_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_value_2052_);
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2063_, v_x_2064_);
lean_dec(v_x_2064_);
lean_dec_ref(v_a_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_buckets_2068_; lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v_fold_2077_; uint64_t v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_buckets_2068_ = lean_ctor_get(v_m_2066_, 1);
v_fst_2069_ = lean_ctor_get(v_a_2067_, 0);
v_snd_2070_ = lean_ctor_get(v_a_2067_, 1);
v___x_2071_ = lean_array_get_size(v_buckets_2068_);
v___x_2072_ = l_Lean_Expr_hash(v_fst_2069_);
v___x_2073_ = l_Lean_Expr_hash(v_snd_2070_);
v___x_2074_ = lean_uint64_mix_hash(v___x_2072_, v___x_2073_);
v___x_2075_ = 32ULL;
v___x_2076_ = lean_uint64_shift_right(v___x_2074_, v___x_2075_);
v_fold_2077_ = lean_uint64_xor(v___x_2074_, v___x_2076_);
v___x_2078_ = 16ULL;
v___x_2079_ = lean_uint64_shift_right(v_fold_2077_, v___x_2078_);
v___x_2080_ = lean_uint64_xor(v_fold_2077_, v___x_2079_);
v___x_2081_ = lean_uint64_to_usize(v___x_2080_);
v___x_2082_ = lean_usize_of_nat(v___x_2071_);
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_sub(v___x_2082_, v___x_2083_);
v___x_2085_ = lean_usize_land(v___x_2081_, v___x_2084_);
v___x_2086_ = lean_array_uget_borrowed(v_buckets_2068_, v___x_2085_);
v___x_2087_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2067_, v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2088_, v_a_2089_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_m_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2091_, uint8_t v___x_2092_, lean_object* v_fst_2093_, lean_object* v_snd_2094_, lean_object* v___x_2095_, lean_object* v_____r_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2108_ = lean_unsigned_to_nat(2u);
v___x_2109_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1, v_a_2091_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1 + 1, v___x_2092_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_fst_2093_);
lean_ctor_set(v___x_2111_, 1, v_snd_2094_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2095_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2110_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2116_ = _args[0];
lean_object* v___x_2117_ = _args[1];
lean_object* v_fst_2118_ = _args[2];
lean_object* v_snd_2119_ = _args[3];
lean_object* v___x_2120_ = _args[4];
lean_object* v_____r_2121_ = _args[5];
lean_object* v___y_2122_ = _args[6];
lean_object* v___y_2123_ = _args[7];
lean_object* v___y_2124_ = _args[8];
lean_object* v___y_2125_ = _args[9];
lean_object* v___y_2126_ = _args[10];
lean_object* v___y_2127_ = _args[11];
lean_object* v___y_2128_ = _args[12];
lean_object* v___y_2129_ = _args[13];
lean_object* v___y_2130_ = _args[14];
lean_object* v___y_2131_ = _args[15];
lean_object* v___y_2132_ = _args[16];
_start:
{
uint8_t v_a_34317__boxed_2133_; uint8_t v___x_34318__boxed_2134_; lean_object* v_res_2135_; 
v_a_34317__boxed_2133_ = lean_unbox(v_a_2116_);
v___x_34318__boxed_2134_ = lean_unbox(v___x_2117_);
v_res_2135_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34317__boxed_2133_, v___x_34318__boxed_2134_, v_fst_2118_, v_snd_2119_, v___x_2120_, v_____r_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec(v___y_2122_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2136_, lean_object* v_snd_2137_, lean_object* v___x_2138_, lean_object* v___x_2139_, lean_object* v_____r_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2152_ = l_Lean_Expr_appFn_x21(v_fst_2136_);
v___x_2153_ = l_Lean_Expr_appFn_x21(v_snd_2137_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2138_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2139_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2159_, lean_object* v_snd_2160_, lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v_____r_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2159_, v_snd_2160_, v___x_2161_, v___x_2162_, v_____r_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v_snd_2160_);
lean_dec(v_fst_2159_);
return v_res_2175_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___f_2177_; 
v___x_2176_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2177_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2177_, 0, v___x_2176_);
return v___f_2177_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2183_ = l_Lean_Name_append(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2202_, lean_object* v___y_2203_, lean_object* v_eq_2204_, lean_object* v_a_2205_, lean_object* v_b_2206_, lean_object* v_a_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___y_2220_; lean_object* v_snd_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2362_; 
v_snd_2240_ = lean_ctor_get(v_a_2207_, 1);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_a_2207_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v_a_2207_, 0);
lean_dec(v_unused_2363_);
v___x_2242_ = v_a_2207_;
v_isShared_2243_ = v_isSharedCheck_2362_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_snd_2240_);
lean_dec(v_a_2207_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2362_;
goto v_resetjp_2241_;
}
v___jp_2219_:
{
if (lean_obj_tag(v___y_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2231_; 
v_a_2221_ = lean_ctor_get(v___y_2220_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___y_2220_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2223_ = v___y_2220_;
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___y_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
if (lean_obj_tag(v_a_2221_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; 
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2225_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v_a_2221_, 1);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_a_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_object* v_a_2229_; 
lean_del_object(v___x_2223_);
v_a_2229_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v_a_2221_, 1);
v_a_2207_ = v_a_2229_;
goto _start;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2232_ = lean_ctor_get(v___y_2220_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___y_2220_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___y_2220_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___y_2220_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
v_resetjp_2241_:
{
lean_object* v_snd_2244_; lean_object* v_fst_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2361_; 
v_snd_2244_ = lean_ctor_get(v_snd_2240_, 1);
v_fst_2245_ = lean_ctor_get(v_snd_2240_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_snd_2240_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2247_ = v_snd_2240_;
v_isShared_2248_ = v_isSharedCheck_2361_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snd_2244_);
lean_inc(v_fst_2245_);
lean_dec(v_snd_2240_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2361_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_fst_2249_; lean_object* v_snd_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2360_; 
v_fst_2249_ = lean_ctor_get(v_snd_2244_, 0);
v_snd_2250_ = lean_ctor_get(v_snd_2244_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_snd_2244_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2252_ = v_snd_2244_;
v_isShared_2253_ = v_isSharedCheck_2360_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_snd_2250_);
lean_inc(v_fst_2249_);
lean_dec(v_snd_2244_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2360_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
uint8_t v___y_2255_; uint8_t v___x_2269_; 
v___x_2269_ = l_Lean_Expr_isApp(v_fst_2249_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v___y_2255_ = v_a_2202_;
goto v___jp_2254_;
}
else
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Expr_isApp(v_snd_2250_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v___y_2255_ = v___x_2270_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; uint8_t v___x_2275_; 
lean_del_object(v___x_2252_);
lean_del_object(v___x_2247_);
lean_del_object(v___x_2242_);
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_sub(v_fst_2245_, v___x_2272_);
lean_dec(v_fst_2245_);
v___f_2274_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2203_);
lean_inc(v___x_2273_);
v___x_2275_ = l_List_elem___redArg(v___f_2274_, v___x_2273_, v___y_2203_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_Expr_appArg_x21(v_fst_2249_);
v___x_2277_ = l_Lean_Expr_appArg_x21(v_snd_2250_);
v___x_2278_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2276_, v___x_2277_, v___y_2208_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; uint8_t v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = lean_unbox(v_a_2279_);
if (v___x_2280_ == 0)
{
lean_object* v_toCold_2281_; lean_object* v_options_2282_; lean_object* v_inheritedTraceOptions_2283_; uint8_t v_hasTrace_2284_; 
v_toCold_2281_ = lean_ctor_get(v___y_2216_, 0);
v_options_2282_ = lean_ctor_get(v_toCold_2281_, 2);
v_inheritedTraceOptions_2283_ = lean_ctor_get(v_toCold_2281_, 11);
v_hasTrace_2284_ = lean_ctor_get_uint8(v_options_2282_, sizeof(void*)*1);
if (v_hasTrace_2284_ == 0)
{
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
goto v___jp_2285_;
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2290_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2291_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2283_, v_options_2282_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
goto v___jp_2285_;
}
else
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Meta_Grind_updateLastTag(v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2292_, 1);
v___x_2293_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2204_, v___y_2208_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2295_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2205_);
v___x_2296_ = l_Lean_MessageData_ofExpr(v_a_2205_);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
lean_inc_ref(v_b_2206_);
v___x_2300_ = l_Lean_MessageData_ofExpr(v_b_2206_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
lean_inc_ref(v_eq_2204_);
v___x_2304_ = l_Lean_MessageData_ofExpr(v_eq_2204_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_MessageData_ofExpr(v___x_2276_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l_Lean_MessageData_ofExpr(v___x_2277_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Nat_reprFast(v_a_2294_);
v___x_2317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
v___x_2318_ = l_Lean_MessageData_ofFormat(v___x_2317_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2315_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2289_, v___x_2319_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = lean_unbox(v_a_2279_);
lean_dec(v_a_2279_);
v___x_2323_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2322_, v___x_2270_, v_fst_2249_, v_snd_2250_, v___x_2273_, v_a_2321_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
v___y_2220_ = v___x_2323_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_a_2279_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2324_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2320_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2320_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2332_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2293_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2293_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2340_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2292_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2292_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
v___jp_2285_:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_unbox(v_a_2279_);
lean_dec(v_a_2279_);
v___x_2288_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2287_, v___x_2270_, v_fst_2249_, v_snd_2250_, v___x_2273_, v___x_2286_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
v___y_2220_ = v___x_2288_;
goto v___jp_2219_;
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
v___x_2348_ = lean_box(0);
v___x_2349_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2249_, v_snd_2250_, v___x_2273_, v___x_2271_, v___x_2348_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
v___y_2220_ = v___x_2349_;
goto v___jp_2219_;
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2350_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2278_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2278_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2249_, v_snd_2250_, v___x_2273_, v___x_2271_, v___x_2358_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
v___y_2220_ = v___x_2359_;
goto v___jp_2219_;
}
}
}
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
v___x_2257_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1, v___y_2255_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1 + 1, v___y_2255_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
if (v_isShared_2253_ == 0)
{
v___x_2260_ = v___x_2252_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_fst_2249_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_snd_2250_);
v___x_2260_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2262_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v___x_2260_);
v___x_2262_ = v___x_2247_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_fst_2245_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 1, v___x_2262_);
lean_ctor_set(v___x_2242_, 0, v___x_2258_);
v___x_2264_ = v___x_2242_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
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
lean_object* v_a_2364_ = _args[0];
lean_object* v___y_2365_ = _args[1];
lean_object* v_eq_2366_ = _args[2];
lean_object* v_a_2367_ = _args[3];
lean_object* v_b_2368_ = _args[4];
lean_object* v_a_2369_ = _args[5];
lean_object* v___y_2370_ = _args[6];
lean_object* v___y_2371_ = _args[7];
lean_object* v___y_2372_ = _args[8];
lean_object* v___y_2373_ = _args[9];
lean_object* v___y_2374_ = _args[10];
lean_object* v___y_2375_ = _args[11];
lean_object* v___y_2376_ = _args[12];
lean_object* v___y_2377_ = _args[13];
lean_object* v___y_2378_ = _args[14];
lean_object* v___y_2379_ = _args[15];
lean_object* v___y_2380_ = _args[16];
_start:
{
uint8_t v_a_34491__boxed_2381_; lean_object* v_res_2382_; 
v_a_34491__boxed_2381_ = lean_unbox(v_a_2364_);
v_res_2382_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34491__boxed_2381_, v___y_2365_, v_eq_2366_, v_a_2367_, v_b_2368_, v_a_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2383_, lean_object* v_b_2384_, lean_object* v_eq_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2400_; 
lean_inc_ref(v_eq_2385_);
v___x_2400_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2385_, v_a_2386_, v_a_2390_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; uint8_t v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = lean_unbox(v_a_2401_);
lean_dec(v_a_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; 
lean_inc_ref(v_eq_2385_);
v___x_2403_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2385_, v_a_2386_, v_a_2390_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; uint8_t v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = lean_unbox(v_a_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___y_2408_; lean_object* v_toGoalState_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2453_; 
v___x_2406_ = lean_st_ref_get(v_a_2386_);
v_toGoalState_2441_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2406_, 1);
lean_dec(v_unused_2454_);
v___x_2443_ = v___x_2406_;
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_toGoalState_2441_);
lean_dec(v___x_2406_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2409_ = l_Lean_Expr_getAppNumArgs(v_a_2383_);
v___x_2410_ = lean_box(0);
lean_inc_ref(v_b_2384_);
lean_inc_ref(v_a_2383_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_a_2383_);
lean_ctor_set(v___x_2411_, 1, v_b_2384_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2409_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_unbox(v_a_2404_);
v___x_2415_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___x_2414_, v___y_2408_, v_eq_2385_, v_a_2383_, v_b_2384_, v___x_2413_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2432_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2432_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2432_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_fst_2420_; 
v_fst_2420_ = lean_ctor_get(v_a_2416_, 0);
lean_inc(v_fst_2420_);
lean_dec(v_a_2416_);
if (lean_obj_tag(v_fst_2420_) == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2426_; 
v___x_2421_ = lean_unsigned_to_nat(2u);
v___x_2422_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
v___x_2423_ = lean_unbox(v_a_2404_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1, v___x_2423_);
v___x_2424_ = lean_unbox(v_a_2404_);
lean_dec(v_a_2404_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1 + 1, v___x_2424_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2422_);
v___x_2426_ = v___x_2418_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2422_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
else
{
lean_object* v_val_2428_; lean_object* v___x_2430_; 
lean_dec(v_a_2404_);
v_val_2428_ = lean_ctor_get(v_fst_2420_, 0);
lean_inc(v_val_2428_);
lean_dec_ref_known(v_fst_2420_, 1);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v_val_2428_);
v___x_2430_ = v___x_2418_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_val_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_a_2404_);
v_a_2433_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2415_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2415_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
v_resetjp_2442_:
{
lean_object* v_split_2445_; lean_object* v_argPosMap_2446_; lean_object* v___x_2448_; 
v_split_2445_ = lean_ctor_get(v_toGoalState_2441_, 15);
lean_inc_ref(v_split_2445_);
lean_dec_ref(v_toGoalState_2441_);
v_argPosMap_2446_ = lean_ctor_get(v_split_2445_, 5);
lean_inc_ref(v_argPosMap_2446_);
lean_dec_ref(v_split_2445_);
lean_inc_ref(v_b_2384_);
lean_inc_ref(v_a_2383_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v_b_2384_);
lean_ctor_set(v___x_2443_, 0, v_a_2383_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2383_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_b_2384_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2446_, v___x_2448_);
lean_dec_ref(v___x_2448_);
lean_dec_ref(v_argPosMap_2446_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_box(0);
v___y_2408_ = v___x_2450_;
goto v___jp_2407_;
}
else
{
lean_object* v_val_2451_; 
v_val_2451_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v___x_2449_, 1);
v___y_2408_ = v_val_2451_;
goto v___jp_2407_;
}
}
}
}
else
{
lean_dec(v_a_2404_);
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
goto v___jp_2397_;
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
v_a_2455_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2403_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2403_);
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
else
{
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
goto v___jp_2397_;
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
v_a_2463_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2400_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2400_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2471_, lean_object* v_b_2472_, lean_object* v_eq_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2471_, v_b_2472_, v_eq_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec(v_a_2474_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2486_, lean_object* v___y_2487_, lean_object* v_eq_2488_, lean_object* v_a_2489_, lean_object* v_b_2490_, lean_object* v_inst_2491_, lean_object* v_a_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2486_, v___y_2487_, v_eq_2488_, v_a_2489_, v_b_2490_, v_a_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2505_ = _args[0];
lean_object* v___y_2506_ = _args[1];
lean_object* v_eq_2507_ = _args[2];
lean_object* v_a_2508_ = _args[3];
lean_object* v_b_2509_ = _args[4];
lean_object* v_inst_2510_ = _args[5];
lean_object* v_a_2511_ = _args[6];
lean_object* v___y_2512_ = _args[7];
lean_object* v___y_2513_ = _args[8];
lean_object* v___y_2514_ = _args[9];
lean_object* v___y_2515_ = _args[10];
lean_object* v___y_2516_ = _args[11];
lean_object* v___y_2517_ = _args[12];
lean_object* v___y_2518_ = _args[13];
lean_object* v___y_2519_ = _args[14];
lean_object* v___y_2520_ = _args[15];
lean_object* v___y_2521_ = _args[16];
lean_object* v___y_2522_ = _args[17];
_start:
{
uint8_t v_a_34972__boxed_2523_; lean_object* v_res_2524_; 
v_a_34972__boxed_2523_ = lean_unbox(v_a_2505_);
v_res_2524_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34972__boxed_2523_, v___y_2506_, v_eq_2507_, v_a_2508_, v_b_2509_, v_inst_2510_, v_a_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec(v___y_2512_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2525_, lean_object* v_m_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2526_, v_a_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2529_, lean_object* v_m_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2529_, v_m_2530_, v_a_2531_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_m_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2533_, lean_object* v_a_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2534_, v_x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2537_, lean_object* v_a_2538_, lean_object* v_x_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2537_, v_a_2538_, v_x_2539_);
lean_dec(v_x_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2555_; 
lean_inc_ref(v_imp_2541_);
v___x_2555_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; uint8_t v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2572_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2572_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2572_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
uint8_t v___x_2563_; 
v___x_2563_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_box(1);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2564_);
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_box(0);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2568_);
v___x_2570_ = v___x_2561_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2558_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2558_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v_binderType_2581_; lean_object* v_body_2582_; lean_object* v___x_2583_; 
v_binderType_2581_ = lean_ctor_get(v_imp_2541_, 1);
lean_inc_ref_n(v_binderType_2581_, 2);
v_body_2582_ = lean_ctor_get(v_imp_2541_, 2);
lean_inc_ref(v_body_2582_);
lean_dec_ref(v_imp_2541_);
v___x_2583_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2581_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; uint8_t v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = lean_unbox(v_a_2584_);
lean_dec(v_a_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2581_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2623_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2623_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2623_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_unbox(v_a_2587_);
if (v___x_2599_ == 0)
{
uint8_t v___x_2600_; 
v___x_2600_ = l_Lean_Expr_hasLooseBVars(v_body_2582_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
lean_inc_ref(v_body_2582_);
v___x_2601_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2582_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; uint8_t v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = lean_unbox(v_a_2602_);
lean_dec(v_a_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2582_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; uint8_t v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_unbox(v_a_2605_);
lean_dec(v_a_2605_);
if (v___x_2606_ == 0)
{
goto v___jp_2591_;
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
goto v___jp_2549_;
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
v_a_2607_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2604_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2604_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec_ref(v_body_2582_);
goto v___jp_2549_;
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec_ref(v_body_2582_);
v_a_2615_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2601_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2601_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_dec_ref(v_body_2582_);
goto v___jp_2591_;
}
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec_ref(v_body_2582_);
goto v___jp_2552_;
}
v___jp_2591_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; uint8_t v___x_2595_; lean_object* v___x_2597_; 
v___x_2592_ = lean_unsigned_to_nat(2u);
v___x_2593_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
v___x_2594_ = lean_unbox(v_a_2587_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*1, v___x_2594_);
v___x_2595_ = lean_unbox(v_a_2587_);
lean_dec(v_a_2587_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*1 + 1, v___x_2595_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2593_);
v___x_2597_ = v___x_2589_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2593_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_body_2582_);
v_a_2624_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2586_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2586_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_dec_ref(v_body_2582_);
lean_dec_ref(v_binderType_2581_);
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_body_2582_);
lean_dec_ref(v_binderType_2581_);
v_a_2632_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2583_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2583_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v_imp_2541_);
v_a_2640_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2555_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2555_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
v___jp_2549_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
v___jp_2552_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2657_, lean_object* v_h_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2657_, v_a_2659_, v_a_2663_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2671_, lean_object* v_h_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2671_, v_h_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec(v_a_2673_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
switch(lean_obj_tag(v_s_2685_))
{
case 0:
{
lean_object* v_e_2697_; lean_object* v___x_2698_; 
v_e_2697_ = lean_ctor_get(v_s_2685_, 0);
lean_inc_ref(v_e_2697_);
lean_dec_ref_known(v_s_2685_, 2);
v___x_2698_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2697_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2698_;
}
case 1:
{
lean_object* v_e_2699_; lean_object* v___x_2700_; 
v_e_2699_ = lean_ctor_get(v_s_2685_, 0);
lean_inc_ref(v_e_2699_);
lean_dec_ref_known(v_s_2685_, 2);
v___x_2700_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2699_, v_a_2686_, v_a_2690_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2700_;
}
default: 
{
lean_object* v_a_2701_; lean_object* v_b_2702_; lean_object* v_eq_2703_; lean_object* v___x_2704_; 
v_a_2701_ = lean_ctor_get(v_s_2685_, 0);
lean_inc_ref(v_a_2701_);
v_b_2702_ = lean_ctor_get(v_s_2685_, 1);
lean_inc_ref(v_b_2702_);
v_eq_2703_ = lean_ctor_get(v_s_2685_, 3);
lean_inc_ref(v_eq_2703_);
lean_dec_ref_known(v_s_2685_, 5);
v___x_2704_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2701_, v_b_2702_, v_eq_2703_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec(v_a_2706_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_tag_nat(v_x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2720_);
lean_dec(v_x_2720_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2722_, lean_object* v_k_2723_){
_start:
{
if (lean_obj_tag(v_t_2722_) == 0)
{
return v_k_2723_;
}
else
{
lean_object* v_c_2724_; lean_object* v_numCases_2725_; uint8_t v_isRec_2726_; uint8_t v_tryPostpone_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_c_2724_ = lean_ctor_get(v_t_2722_, 0);
lean_inc_ref(v_c_2724_);
v_numCases_2725_ = lean_ctor_get(v_t_2722_, 1);
lean_inc(v_numCases_2725_);
v_isRec_2726_ = lean_ctor_get_uint8(v_t_2722_, sizeof(void*)*2);
v_tryPostpone_2727_ = lean_ctor_get_uint8(v_t_2722_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2722_, 2);
v___x_2728_ = lean_box(v_isRec_2726_);
v___x_2729_ = lean_box(v_tryPostpone_2727_);
v___x_2730_ = lean_apply_4(v_k_2723_, v_c_2724_, v_numCases_2725_, v___x_2728_, v___x_2729_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2731_, lean_object* v_ctorIdx_2732_, lean_object* v_t_2733_, lean_object* v_h_2734_, lean_object* v_k_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2733_, v_k_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2737_, lean_object* v_ctorIdx_2738_, lean_object* v_t_2739_, lean_object* v_h_2740_, lean_object* v_k_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2737_, v_ctorIdx_2738_, v_t_2739_, v_h_2740_, v_k_2741_);
lean_dec(v_ctorIdx_2738_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2743_, lean_object* v_none_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2743_, v_none_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2746_, lean_object* v_t_2747_, lean_object* v_h_2748_, lean_object* v_none_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2747_, v_none_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2751_, lean_object* v_some_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2751_, v_some_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2754_, lean_object* v_t_2755_, lean_object* v_h_2756_, lean_object* v_some_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2755_, v_some_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2759_, lean_object* v_as_2760_, size_t v_i_2761_, size_t v_stop_2762_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_eq(v_i_2761_, v_stop_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = lean_array_uget_borrowed(v_as_2760_, v_i_2761_);
v___x_2765_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2764_, v_a_2759_);
if (v___x_2765_ == 0)
{
size_t v___x_2766_; size_t v___x_2767_; 
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_add(v_i_2761_, v___x_2766_);
v_i_2761_ = v___x_2767_;
goto _start;
}
else
{
return v___x_2765_;
}
}
else
{
uint8_t v___x_2769_; 
v___x_2769_ = 0;
return v___x_2769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2770_, lean_object* v_as_2771_, lean_object* v_i_2772_, lean_object* v_stop_2773_){
_start:
{
uint64_t v_a_2507__boxed_2774_; size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; uint8_t v_res_2777_; lean_object* v_r_2778_; 
v_a_2507__boxed_2774_ = lean_unbox_uint64(v_a_2770_);
lean_dec_ref(v_a_2770_);
v_i_boxed_2775_ = lean_unbox_usize(v_i_2772_);
lean_dec(v_i_2772_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2773_);
lean_dec(v_stop_2773_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2774_, v_as_2771_, v_i_boxed_2775_, v_stop_boxed_2776_);
lean_dec_ref(v_as_2771_);
v_r_2778_ = lean_box(v_res_2777_);
return v_r_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2781_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2834_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2834_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2834_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
if (lean_obj_tag(v_a_2791_) == 1)
{
lean_object* v_val_2795_; lean_object* v___x_2796_; 
lean_del_object(v___x_2793_);
v_val_2795_ = lean_ctor_get(v_a_2791_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v_a_2791_, 1);
v___x_2796_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2820_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = lean_array_get_size(v_val_2795_);
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_dec(v_a_2797_);
lean_dec(v_val_2795_);
v___x_2804_ = lean_box(v___x_2803_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2804_);
v___x_2806_ = v___x_2799_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
else
{
if (v___x_2803_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
lean_dec(v_a_2797_);
lean_dec(v_val_2795_);
v___x_2808_ = lean_box(v___x_2803_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2808_);
v___x_2810_ = v___x_2799_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
size_t v___x_2812_; size_t v___x_2813_; uint64_t v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2812_ = ((size_t)0ULL);
v___x_2813_ = lean_usize_of_nat(v___x_2802_);
v___x_2814_ = lean_unbox_uint64(v_a_2797_);
lean_dec(v_a_2797_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2814_, v_val_2795_, v___x_2812_, v___x_2813_);
lean_dec(v_val_2795_);
v___x_2816_ = lean_box(v___x_2815_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2816_);
v___x_2818_ = v___x_2799_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec(v_val_2795_);
v_a_2821_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2796_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2796_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_dec(v_a_2791_);
v___x_2829_ = 1;
v___x_2830_ = lean_box(v___x_2829_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2830_);
v___x_2832_ = v___x_2793_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
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
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
v_a_2835_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2790_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2790_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_c_2843_);
return v_res_2854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2857_ = l_Lean_stringToMessageData(v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2858_, lean_object* v_c_x3f_2859_, lean_object* v_cs_x27_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
if (lean_obj_tag(v_cs_2858_) == 0)
{
lean_object* v___x_2872_; lean_object* v_toGoalState_2873_; lean_object* v_split_2874_; lean_object* v_mvarId_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2990_; 
v___x_2872_ = lean_st_ref_take(v_a_2861_);
v_toGoalState_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc_ref(v_toGoalState_2873_);
v_split_2874_ = lean_ctor_get(v_toGoalState_2873_, 15);
lean_inc_ref(v_split_2874_);
v_mvarId_2875_ = lean_ctor_get(v___x_2872_, 1);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2991_);
v___x_2877_ = v___x_2872_;
v_isShared_2878_ = v_isSharedCheck_2990_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_mvarId_2875_);
lean_dec(v___x_2872_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2990_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_nextDeclIdx_2879_; lean_object* v_enodeMap_2880_; lean_object* v_exprs_2881_; lean_object* v_parents_2882_; lean_object* v_congrTable_2883_; lean_object* v_appMap_2884_; lean_object* v_indicesFound_2885_; lean_object* v_toProcess_2886_; lean_object* v_internalizing_2887_; uint8_t v_inconsistent_2888_; lean_object* v_nextIdx_2889_; lean_object* v_newRawFacts_2890_; lean_object* v_facts_2891_; lean_object* v_extThms_2892_; lean_object* v_ematch_2893_; lean_object* v_inj_2894_; lean_object* v_clean_2895_; lean_object* v_sstates_2896_; lean_object* v_goalStack_2897_; uint64_t v_introBase_2898_; lean_object* v_numIntros_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2988_; 
v_nextDeclIdx_2879_ = lean_ctor_get(v_toGoalState_2873_, 0);
v_enodeMap_2880_ = lean_ctor_get(v_toGoalState_2873_, 1);
v_exprs_2881_ = lean_ctor_get(v_toGoalState_2873_, 2);
v_parents_2882_ = lean_ctor_get(v_toGoalState_2873_, 3);
v_congrTable_2883_ = lean_ctor_get(v_toGoalState_2873_, 4);
v_appMap_2884_ = lean_ctor_get(v_toGoalState_2873_, 5);
v_indicesFound_2885_ = lean_ctor_get(v_toGoalState_2873_, 6);
v_toProcess_2886_ = lean_ctor_get(v_toGoalState_2873_, 7);
v_internalizing_2887_ = lean_ctor_get(v_toGoalState_2873_, 8);
v_inconsistent_2888_ = lean_ctor_get_uint8(v_toGoalState_2873_, sizeof(void*)*20 + 8);
v_nextIdx_2889_ = lean_ctor_get(v_toGoalState_2873_, 9);
v_newRawFacts_2890_ = lean_ctor_get(v_toGoalState_2873_, 10);
v_facts_2891_ = lean_ctor_get(v_toGoalState_2873_, 11);
v_extThms_2892_ = lean_ctor_get(v_toGoalState_2873_, 12);
v_ematch_2893_ = lean_ctor_get(v_toGoalState_2873_, 13);
v_inj_2894_ = lean_ctor_get(v_toGoalState_2873_, 14);
v_clean_2895_ = lean_ctor_get(v_toGoalState_2873_, 16);
v_sstates_2896_ = lean_ctor_get(v_toGoalState_2873_, 17);
v_goalStack_2897_ = lean_ctor_get(v_toGoalState_2873_, 18);
v_introBase_2898_ = lean_ctor_get_uint64(v_toGoalState_2873_, sizeof(void*)*20);
v_numIntros_2899_ = lean_ctor_get(v_toGoalState_2873_, 19);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_toGoalState_2873_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v_toGoalState_2873_, 15);
lean_dec(v_unused_2989_);
v___x_2901_ = v_toGoalState_2873_;
v_isShared_2902_ = v_isSharedCheck_2988_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_numIntros_2899_);
lean_inc(v_goalStack_2897_);
lean_inc(v_sstates_2896_);
lean_inc(v_clean_2895_);
lean_inc(v_inj_2894_);
lean_inc(v_ematch_2893_);
lean_inc(v_extThms_2892_);
lean_inc(v_facts_2891_);
lean_inc(v_newRawFacts_2890_);
lean_inc(v_nextIdx_2889_);
lean_inc(v_internalizing_2887_);
lean_inc(v_toProcess_2886_);
lean_inc(v_indicesFound_2885_);
lean_inc(v_appMap_2884_);
lean_inc(v_congrTable_2883_);
lean_inc(v_parents_2882_);
lean_inc(v_exprs_2881_);
lean_inc(v_enodeMap_2880_);
lean_inc(v_nextDeclIdx_2879_);
lean_dec(v_toGoalState_2873_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2988_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v_added_2903_; lean_object* v_resolved_2904_; lean_object* v_trace_2905_; lean_object* v_lookaheads_2906_; lean_object* v_argPosMap_2907_; lean_object* v_argsAt_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2986_; 
v_added_2903_ = lean_ctor_get(v_split_2874_, 1);
v_resolved_2904_ = lean_ctor_get(v_split_2874_, 2);
v_trace_2905_ = lean_ctor_get(v_split_2874_, 3);
v_lookaheads_2906_ = lean_ctor_get(v_split_2874_, 4);
v_argPosMap_2907_ = lean_ctor_get(v_split_2874_, 5);
v_argsAt_2908_ = lean_ctor_get(v_split_2874_, 6);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_split_2874_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v_split_2874_, 0);
lean_dec(v_unused_2987_);
v___x_2910_ = v_split_2874_;
v_isShared_2911_ = v_isSharedCheck_2986_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_argsAt_2908_);
lean_inc(v_argPosMap_2907_);
lean_inc(v_lookaheads_2906_);
lean_inc(v_trace_2905_);
lean_inc(v_resolved_2904_);
lean_inc(v_added_2903_);
lean_dec(v_split_2874_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2986_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = l_List_reverse___redArg(v_cs_x27_2860_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_added_2903_);
lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_resolved_2904_);
lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_trace_2905_);
lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_lookaheads_2906_);
lean_ctor_set(v_reuseFailAlloc_2985_, 5, v_argPosMap_2907_);
lean_ctor_set(v_reuseFailAlloc_2985_, 6, v_argsAt_2908_);
v___x_2914_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 15, v___x_2914_);
v___x_2916_ = v___x_2901_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_nextDeclIdx_2879_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_enodeMap_2880_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_exprs_2881_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_parents_2882_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_congrTable_2883_);
lean_ctor_set(v_reuseFailAlloc_2984_, 5, v_appMap_2884_);
lean_ctor_set(v_reuseFailAlloc_2984_, 6, v_indicesFound_2885_);
lean_ctor_set(v_reuseFailAlloc_2984_, 7, v_toProcess_2886_);
lean_ctor_set(v_reuseFailAlloc_2984_, 8, v_internalizing_2887_);
lean_ctor_set(v_reuseFailAlloc_2984_, 9, v_nextIdx_2889_);
lean_ctor_set(v_reuseFailAlloc_2984_, 10, v_newRawFacts_2890_);
lean_ctor_set(v_reuseFailAlloc_2984_, 11, v_facts_2891_);
lean_ctor_set(v_reuseFailAlloc_2984_, 12, v_extThms_2892_);
lean_ctor_set(v_reuseFailAlloc_2984_, 13, v_ematch_2893_);
lean_ctor_set(v_reuseFailAlloc_2984_, 14, v_inj_2894_);
lean_ctor_set(v_reuseFailAlloc_2984_, 15, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2984_, 16, v_clean_2895_);
lean_ctor_set(v_reuseFailAlloc_2984_, 17, v_sstates_2896_);
lean_ctor_set(v_reuseFailAlloc_2984_, 18, v_goalStack_2897_);
lean_ctor_set(v_reuseFailAlloc_2984_, 19, v_numIntros_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2984_, sizeof(void*)*20 + 8, v_inconsistent_2888_);
lean_ctor_set_uint64(v_reuseFailAlloc_2984_, sizeof(void*)*20, v_introBase_2898_);
v___x_2916_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2916_);
v___x_2918_ = v___x_2877_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_mvarId_2875_);
v___x_2918_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_st_ref_put(v_a_2861_, v___x_2918_);
if (lean_obj_tag(v_c_x3f_2859_) == 1)
{
lean_object* v___x_2920_; lean_object* v_toGoalState_2921_; lean_object* v_ematch_2922_; lean_object* v_mvarId_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2980_; 
v___x_2920_ = lean_st_ref_take(v_a_2861_);
v_toGoalState_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_toGoalState_2921_);
v_ematch_2922_ = lean_ctor_get(v_toGoalState_2921_, 13);
lean_inc_ref(v_ematch_2922_);
v_mvarId_2923_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2981_);
v___x_2925_ = v___x_2920_;
v_isShared_2926_ = v_isSharedCheck_2980_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_mvarId_2923_);
lean_dec(v___x_2920_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2980_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_nextDeclIdx_2927_; lean_object* v_enodeMap_2928_; lean_object* v_exprs_2929_; lean_object* v_parents_2930_; lean_object* v_congrTable_2931_; lean_object* v_appMap_2932_; lean_object* v_indicesFound_2933_; lean_object* v_toProcess_2934_; lean_object* v_internalizing_2935_; uint8_t v_inconsistent_2936_; lean_object* v_nextIdx_2937_; lean_object* v_newRawFacts_2938_; lean_object* v_facts_2939_; lean_object* v_extThms_2940_; lean_object* v_inj_2941_; lean_object* v_split_2942_; lean_object* v_clean_2943_; lean_object* v_sstates_2944_; lean_object* v_goalStack_2945_; uint64_t v_introBase_2946_; lean_object* v_numIntros_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2978_; 
v_nextDeclIdx_2927_ = lean_ctor_get(v_toGoalState_2921_, 0);
v_enodeMap_2928_ = lean_ctor_get(v_toGoalState_2921_, 1);
v_exprs_2929_ = lean_ctor_get(v_toGoalState_2921_, 2);
v_parents_2930_ = lean_ctor_get(v_toGoalState_2921_, 3);
v_congrTable_2931_ = lean_ctor_get(v_toGoalState_2921_, 4);
v_appMap_2932_ = lean_ctor_get(v_toGoalState_2921_, 5);
v_indicesFound_2933_ = lean_ctor_get(v_toGoalState_2921_, 6);
v_toProcess_2934_ = lean_ctor_get(v_toGoalState_2921_, 7);
v_internalizing_2935_ = lean_ctor_get(v_toGoalState_2921_, 8);
v_inconsistent_2936_ = lean_ctor_get_uint8(v_toGoalState_2921_, sizeof(void*)*20 + 8);
v_nextIdx_2937_ = lean_ctor_get(v_toGoalState_2921_, 9);
v_newRawFacts_2938_ = lean_ctor_get(v_toGoalState_2921_, 10);
v_facts_2939_ = lean_ctor_get(v_toGoalState_2921_, 11);
v_extThms_2940_ = lean_ctor_get(v_toGoalState_2921_, 12);
v_inj_2941_ = lean_ctor_get(v_toGoalState_2921_, 14);
v_split_2942_ = lean_ctor_get(v_toGoalState_2921_, 15);
v_clean_2943_ = lean_ctor_get(v_toGoalState_2921_, 16);
v_sstates_2944_ = lean_ctor_get(v_toGoalState_2921_, 17);
v_goalStack_2945_ = lean_ctor_get(v_toGoalState_2921_, 18);
v_introBase_2946_ = lean_ctor_get_uint64(v_toGoalState_2921_, sizeof(void*)*20);
v_numIntros_2947_ = lean_ctor_get(v_toGoalState_2921_, 19);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_toGoalState_2921_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_toGoalState_2921_, 13);
lean_dec(v_unused_2979_);
v___x_2949_ = v_toGoalState_2921_;
v_isShared_2950_ = v_isSharedCheck_2978_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_numIntros_2947_);
lean_inc(v_goalStack_2945_);
lean_inc(v_sstates_2944_);
lean_inc(v_clean_2943_);
lean_inc(v_split_2942_);
lean_inc(v_inj_2941_);
lean_inc(v_extThms_2940_);
lean_inc(v_facts_2939_);
lean_inc(v_newRawFacts_2938_);
lean_inc(v_nextIdx_2937_);
lean_inc(v_internalizing_2935_);
lean_inc(v_toProcess_2934_);
lean_inc(v_indicesFound_2933_);
lean_inc(v_appMap_2932_);
lean_inc(v_congrTable_2931_);
lean_inc(v_parents_2930_);
lean_inc(v_exprs_2929_);
lean_inc(v_enodeMap_2928_);
lean_inc(v_nextDeclIdx_2927_);
lean_dec(v_toGoalState_2921_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2978_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_thmMap_2951_; lean_object* v_gmt_2952_; lean_object* v_thms_2953_; lean_object* v_newThms_2954_; lean_object* v_numInstances_2955_; lean_object* v_numDelayedInstances_2956_; lean_object* v_preInstances_2957_; lean_object* v_nextThmIdx_2958_; lean_object* v_matchEqNames_2959_; lean_object* v_delayedThmInsts_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2976_; 
v_thmMap_2951_ = lean_ctor_get(v_ematch_2922_, 0);
v_gmt_2952_ = lean_ctor_get(v_ematch_2922_, 1);
v_thms_2953_ = lean_ctor_get(v_ematch_2922_, 2);
v_newThms_2954_ = lean_ctor_get(v_ematch_2922_, 3);
v_numInstances_2955_ = lean_ctor_get(v_ematch_2922_, 4);
v_numDelayedInstances_2956_ = lean_ctor_get(v_ematch_2922_, 5);
v_preInstances_2957_ = lean_ctor_get(v_ematch_2922_, 7);
v_nextThmIdx_2958_ = lean_ctor_get(v_ematch_2922_, 8);
v_matchEqNames_2959_ = lean_ctor_get(v_ematch_2922_, 9);
v_delayedThmInsts_2960_ = lean_ctor_get(v_ematch_2922_, 10);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_ematch_2922_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_ematch_2922_, 6);
lean_dec(v_unused_2977_);
v___x_2962_ = v_ematch_2922_;
v_isShared_2963_ = v_isSharedCheck_2976_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_delayedThmInsts_2960_);
lean_inc(v_matchEqNames_2959_);
lean_inc(v_nextThmIdx_2958_);
lean_inc(v_preInstances_2957_);
lean_inc(v_numDelayedInstances_2956_);
lean_inc(v_numInstances_2955_);
lean_inc(v_newThms_2954_);
lean_inc(v_thms_2953_);
lean_inc(v_gmt_2952_);
lean_inc(v_thmMap_2951_);
lean_dec(v_ematch_2922_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2976_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = lean_unsigned_to_nat(0u);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 6, v___x_2964_);
v___x_2966_ = v___x_2962_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_thmMap_2951_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_gmt_2952_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_thms_2953_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_newThms_2954_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_numInstances_2955_);
lean_ctor_set(v_reuseFailAlloc_2975_, 5, v_numDelayedInstances_2956_);
lean_ctor_set(v_reuseFailAlloc_2975_, 6, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2975_, 7, v_preInstances_2957_);
lean_ctor_set(v_reuseFailAlloc_2975_, 8, v_nextThmIdx_2958_);
lean_ctor_set(v_reuseFailAlloc_2975_, 9, v_matchEqNames_2959_);
lean_ctor_set(v_reuseFailAlloc_2975_, 10, v_delayedThmInsts_2960_);
v___x_2966_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 13, v___x_2966_);
v___x_2968_ = v___x_2949_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_nextDeclIdx_2927_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_enodeMap_2928_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_exprs_2929_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_parents_2930_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_congrTable_2931_);
lean_ctor_set(v_reuseFailAlloc_2974_, 5, v_appMap_2932_);
lean_ctor_set(v_reuseFailAlloc_2974_, 6, v_indicesFound_2933_);
lean_ctor_set(v_reuseFailAlloc_2974_, 7, v_toProcess_2934_);
lean_ctor_set(v_reuseFailAlloc_2974_, 8, v_internalizing_2935_);
lean_ctor_set(v_reuseFailAlloc_2974_, 9, v_nextIdx_2937_);
lean_ctor_set(v_reuseFailAlloc_2974_, 10, v_newRawFacts_2938_);
lean_ctor_set(v_reuseFailAlloc_2974_, 11, v_facts_2939_);
lean_ctor_set(v_reuseFailAlloc_2974_, 12, v_extThms_2940_);
lean_ctor_set(v_reuseFailAlloc_2974_, 13, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2974_, 14, v_inj_2941_);
lean_ctor_set(v_reuseFailAlloc_2974_, 15, v_split_2942_);
lean_ctor_set(v_reuseFailAlloc_2974_, 16, v_clean_2943_);
lean_ctor_set(v_reuseFailAlloc_2974_, 17, v_sstates_2944_);
lean_ctor_set(v_reuseFailAlloc_2974_, 18, v_goalStack_2945_);
lean_ctor_set(v_reuseFailAlloc_2974_, 19, v_numIntros_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, sizeof(void*)*20 + 8, v_inconsistent_2936_);
lean_ctor_set_uint64(v_reuseFailAlloc_2974_, sizeof(void*)*20, v_introBase_2946_);
v___x_2968_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2968_);
v___x_2970_ = v___x_2925_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_mvarId_2923_);
v___x_2970_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_st_ref_put(v_a_2861_, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_c_x3f_2859_);
return v___x_2972_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_c_x3f_2859_);
return v___x_2982_;
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
lean_object* v_head_2992_; lean_object* v_tail_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3213_; 
v_head_2992_ = lean_ctor_get(v_cs_2858_, 0);
v_tail_2993_ = lean_ctor_get(v_cs_2858_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_cs_2858_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_2995_ = v_cs_2858_;
v_isShared_2996_ = v_isSharedCheck_3213_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_tail_2993_);
lean_inc(v_head_2992_);
lean_dec(v_cs_2858_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3213_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3013_; lean_object* v___y_3014_; uint8_t v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; uint8_t v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; uint8_t v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; uint8_t v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; uint8_t v___y_3102_; lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2992_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; uint8_t v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
if (v___x_3107_ == 0)
{
lean_del_object(v___x_2995_);
lean_dec(v_head_2992_);
v_cs_2858_ = v_tail_2993_;
goto _start;
}
else
{
lean_object* v_toCold_3109_; lean_object* v_options_3110_; lean_object* v_inheritedTraceOptions_3111_; uint8_t v_hasTrace_3112_; uint8_t v___x_3113_; lean_object* v___y_3115_; lean_object* v___y_3116_; uint8_t v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; uint8_t v___y_3128_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; 
v_toCold_3109_ = lean_ctor_get(v_a_2869_, 0);
v_options_3110_ = lean_ctor_get(v_toCold_3109_, 2);
v_inheritedTraceOptions_3111_ = lean_ctor_get(v_toCold_3109_, 11);
v_hasTrace_3112_ = lean_ctor_get_uint8(v_options_3110_, sizeof(void*)*1);
v___x_3113_ = 0;
if (v_hasTrace_3112_ == 0)
{
v___y_3139_ = v_a_2861_;
v___y_3140_ = v_a_2862_;
v___y_3141_ = v_a_2863_;
v___y_3142_ = v_a_2864_;
v___y_3143_ = v_a_2865_;
v___y_3144_ = v_a_2866_;
v___y_3145_ = v_a_2867_;
v___y_3146_ = v_a_2868_;
v___y_3147_ = v_a_2869_;
v___y_3148_ = v_a_2870_;
goto v___jp_3138_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3182_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3111_, v_options_3110_, v___x_3181_);
if (v___x_3182_ == 0)
{
v___y_3139_ = v_a_2861_;
v___y_3140_ = v_a_2862_;
v___y_3141_ = v_a_2863_;
v___y_3142_ = v_a_2864_;
v___y_3143_ = v_a_2865_;
v___y_3144_ = v_a_2866_;
v___y_3145_ = v_a_2867_;
v___y_3146_ = v_a_2868_;
v___y_3147_ = v_a_2869_;
v___y_3148_ = v_a_2870_;
goto v___jp_3138_;
}
else
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_Meta_Grind_updateLastTag(v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec_ref_known(v___x_3183_, 1);
v___x_3184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3185_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2992_);
v___x_3186_ = l_Lean_MessageData_ofExpr(v___x_3185_);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3184_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3180_, v___x_3187_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_dec_ref_known(v___x_3188_, 1);
v___y_3139_ = v_a_2861_;
v___y_3140_ = v_a_2862_;
v___y_3141_ = v_a_2863_;
v___y_3142_ = v_a_2864_;
v___y_3143_ = v_a_2865_;
v___y_3144_ = v_a_2866_;
v___y_3145_ = v_a_2867_;
v___y_3146_ = v_a_2868_;
v___y_3147_ = v_a_2869_;
v___y_3148_ = v_a_2870_;
goto v___jp_3138_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
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
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3197_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3183_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3183_);
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
v___jp_3114_:
{
if (lean_obj_tag(v_c_x3f_2859_) == 0)
{
lean_object* v___x_3129_; 
lean_del_object(v___x_2995_);
v___x_3129_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3129_, 0, v_head_2992_);
lean_ctor_set(v___x_3129_, 1, v___y_3125_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*2, v___y_3123_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*2 + 1, v___y_3117_);
v_cs_2858_ = v_tail_2993_;
v_c_x3f_2859_ = v___x_3129_;
v_a_2861_ = v___y_3118_;
v_a_2862_ = v___y_3119_;
v_a_2863_ = v___y_3120_;
v_a_2864_ = v___y_3126_;
v_a_2865_ = v___y_3115_;
v_a_2866_ = v___y_3116_;
v_a_2867_ = v___y_3122_;
v_a_2868_ = v___y_3121_;
v_a_2869_ = v___y_3124_;
v_a_2870_ = v___y_3127_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3131_; 
v_tryPostpone_3131_ = lean_ctor_get_uint8(v_c_x3f_2859_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3131_ == 0)
{
if (v___y_3117_ == 0)
{
lean_object* v_c_3132_; lean_object* v_numCases_3133_; 
v_c_3132_ = lean_ctor_get(v_c_x3f_2859_, 0);
v_numCases_3133_ = lean_ctor_get(v_c_x3f_2859_, 1);
lean_inc(v_numCases_3133_);
lean_inc_ref(v_c_3132_);
v___y_3087_ = v___y_3116_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v_c_3132_;
v___y_3093_ = v___y_3120_;
v___y_3094_ = v___y_3121_;
v___y_3095_ = v___y_3122_;
v___y_3096_ = v___y_3123_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3125_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v_numCases_3133_;
v___y_3101_ = v___y_3127_;
v___y_3102_ = v___x_3113_;
goto v___jp_3086_;
}
else
{
lean_dec(v___y_3125_);
v___y_2998_ = v___y_3116_;
v___y_2999_ = v___y_3115_;
v___y_3000_ = v___y_3119_;
v___y_3001_ = v___y_3118_;
v___y_3002_ = v___y_3120_;
v___y_3003_ = v___y_3121_;
v___y_3004_ = v___y_3126_;
v___y_3005_ = v___y_3122_;
v___y_3006_ = v___y_3124_;
v___y_3007_ = v___y_3127_;
goto v___jp_2997_;
}
}
else
{
if (v___y_3117_ == 0)
{
lean_object* v_c_3134_; 
lean_del_object(v___x_2995_);
v_c_3134_ = lean_ctor_get(v_c_x3f_2859_, 0);
lean_inc_ref(v_c_3134_);
lean_dec_ref_known(v_c_x3f_2859_, 2);
v___y_3013_ = v___y_3115_;
v___y_3014_ = v___y_3116_;
v___y_3015_ = v___y_3117_;
v___y_3016_ = v___y_3118_;
v___y_3017_ = v___y_3119_;
v___y_3018_ = v_c_3134_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
v___y_3023_ = v___y_3124_;
v___y_3024_ = v___y_3125_;
v___y_3025_ = v___y_3126_;
v___y_3026_ = v___y_3127_;
goto v___jp_3012_;
}
else
{
if (v___y_3128_ == 0)
{
lean_object* v_c_3135_; lean_object* v_numCases_3136_; 
v_c_3135_ = lean_ctor_get(v_c_x3f_2859_, 0);
v_numCases_3136_ = lean_ctor_get(v_c_x3f_2859_, 1);
lean_inc(v_numCases_3136_);
lean_inc_ref(v_c_3135_);
v___y_3087_ = v___y_3116_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v_c_3135_;
v___y_3093_ = v___y_3120_;
v___y_3094_ = v___y_3121_;
v___y_3095_ = v___y_3122_;
v___y_3096_ = v___y_3123_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3125_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v_numCases_3136_;
v___y_3101_ = v___y_3127_;
v___y_3102_ = v___y_3128_;
goto v___jp_3086_;
}
else
{
lean_object* v_c_3137_; 
lean_del_object(v___x_2995_);
v_c_3137_ = lean_ctor_get(v_c_x3f_2859_, 0);
lean_inc_ref(v_c_3137_);
lean_dec_ref_known(v_c_x3f_2859_, 2);
v___y_3013_ = v___y_3115_;
v___y_3014_ = v___y_3116_;
v___y_3015_ = v___y_3117_;
v___y_3016_ = v___y_3118_;
v___y_3017_ = v___y_3119_;
v___y_3018_ = v_c_3137_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
v___y_3023_ = v___y_3124_;
v___y_3024_ = v___y_3125_;
v___y_3025_ = v___y_3126_;
v___y_3026_ = v___y_3127_;
goto v___jp_3012_;
}
}
}
}
}
v___jp_3138_:
{
lean_object* v___x_3149_; 
lean_inc(v_head_2992_);
v___x_3149_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2992_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3149_, 1);
switch(lean_obj_tag(v_a_3150_))
{
case 0:
{
lean_del_object(v___x_2995_);
lean_dec(v_head_2992_);
v_cs_2858_ = v_tail_2993_;
v_a_2861_ = v___y_3139_;
v_a_2862_ = v___y_3140_;
v_a_2863_ = v___y_3141_;
v_a_2864_ = v___y_3142_;
v_a_2865_ = v___y_3143_;
v_a_2866_ = v___y_3144_;
v_a_2867_ = v___y_3145_;
v_a_2868_ = v___y_3146_;
v_a_2869_ = v___y_3147_;
v_a_2870_ = v___y_3148_;
goto _start;
}
case 1:
{
lean_object* v___x_3152_; 
lean_del_object(v___x_2995_);
v___x_3152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_head_2992_);
lean_ctor_set(v___x_3152_, 1, v_cs_x27_2860_);
v_cs_2858_ = v_tail_2993_;
v_cs_x27_2860_ = v___x_3152_;
v_a_2861_ = v___y_3139_;
v_a_2862_ = v___y_3140_;
v_a_2863_ = v___y_3141_;
v_a_2864_ = v___y_3142_;
v_a_2865_ = v___y_3143_;
v_a_2866_ = v___y_3144_;
v_a_2867_ = v___y_3145_;
v_a_2868_ = v___y_3146_;
v_a_2869_ = v___y_3147_;
v_a_2870_ = v___y_3148_;
goto _start;
}
default: 
{
lean_object* v_numCases_3154_; uint8_t v_isRec_3155_; uint8_t v_tryPostpone_3156_; lean_object* v___x_3157_; 
v_numCases_3154_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_numCases_3154_);
v_isRec_3155_ = lean_ctor_get_uint8(v_a_3150_, sizeof(void*)*1);
v_tryPostpone_3156_ = lean_ctor_get_uint8(v_a_3150_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3150_, 1);
v___x_3157_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3141_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; uint8_t v___x_3159_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3159_ = lean_unbox(v_a_3158_);
lean_dec(v_a_3158_);
if (v___x_3159_ == 0)
{
v___y_3115_ = v___y_3143_;
v___y_3116_ = v___y_3144_;
v___y_3117_ = v_tryPostpone_3156_;
v___y_3118_ = v___y_3139_;
v___y_3119_ = v___y_3140_;
v___y_3120_ = v___y_3141_;
v___y_3121_ = v___y_3146_;
v___y_3122_ = v___y_3145_;
v___y_3123_ = v_isRec_3155_;
v___y_3124_ = v___y_3147_;
v___y_3125_ = v_numCases_3154_;
v___y_3126_ = v___y_3142_;
v___y_3127_ = v___y_3148_;
v___y_3128_ = v___x_3113_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = lean_unsigned_to_nat(1u);
v___x_3161_ = lean_nat_dec_lt(v___x_3160_, v_numCases_3154_);
if (v___x_3161_ == 0)
{
v___y_3115_ = v___y_3143_;
v___y_3116_ = v___y_3144_;
v___y_3117_ = v_tryPostpone_3156_;
v___y_3118_ = v___y_3139_;
v___y_3119_ = v___y_3140_;
v___y_3120_ = v___y_3141_;
v___y_3121_ = v___y_3146_;
v___y_3122_ = v___y_3145_;
v___y_3123_ = v_isRec_3155_;
v___y_3124_ = v___y_3147_;
v___y_3125_ = v_numCases_3154_;
v___y_3126_ = v___y_3142_;
v___y_3127_ = v___y_3148_;
v___y_3128_ = v___x_3161_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3162_; 
lean_dec(v_numCases_3154_);
lean_del_object(v___x_2995_);
v___x_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3162_, 0, v_head_2992_);
lean_ctor_set(v___x_3162_, 1, v_cs_x27_2860_);
v_cs_2858_ = v_tail_2993_;
v_cs_x27_2860_ = v___x_3162_;
v_a_2861_ = v___y_3139_;
v_a_2862_ = v___y_3140_;
v_a_2863_ = v___y_3141_;
v_a_2864_ = v___y_3142_;
v_a_2865_ = v___y_3143_;
v_a_2866_ = v___y_3144_;
v_a_2867_ = v___y_3145_;
v_a_2868_ = v___y_3146_;
v_a_2869_ = v___y_3147_;
v_a_2870_ = v___y_3148_;
goto _start;
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_numCases_3154_);
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3164_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3157_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3157_);
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
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3172_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3149_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3149_);
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
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3205_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3105_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3105_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
v___jp_2997_:
{
lean_object* v___x_3009_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v_cs_x27_2860_);
v___x_3009_ = v___x_2995_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_head_2992_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_cs_x27_2860_);
v___x_3009_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v_cs_2858_ = v_tail_2993_;
v_cs_x27_2860_ = v___x_3009_;
v_a_2861_ = v___y_3001_;
v_a_2862_ = v___y_3000_;
v_a_2863_ = v___y_3002_;
v_a_2864_ = v___y_3004_;
v_a_2865_ = v___y_2999_;
v_a_2866_ = v___y_2998_;
v_a_2867_ = v___y_3005_;
v_a_2868_ = v___y_3003_;
v_a_2869_ = v___y_3006_;
v_a_2870_ = v___y_3007_;
goto _start;
}
}
v___jp_3012_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3027_, 0, v_head_2992_);
lean_ctor_set(v___x_3027_, 1, v___y_3024_);
lean_ctor_set_uint8(v___x_3027_, sizeof(void*)*2, v___y_3022_);
lean_ctor_set_uint8(v___x_3027_, sizeof(void*)*2 + 1, v___y_3015_);
v___x_3028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___y_3018_);
lean_ctor_set(v___x_3028_, 1, v_cs_x27_2860_);
v_cs_2858_ = v_tail_2993_;
v_c_x3f_2859_ = v___x_3027_;
v_cs_x27_2860_ = v___x_3028_;
v_a_2861_ = v___y_3016_;
v_a_2862_ = v___y_3017_;
v_a_2863_ = v___y_3019_;
v_a_2864_ = v___y_3025_;
v_a_2865_ = v___y_3013_;
v_a_2866_ = v___y_3014_;
v_a_2867_ = v___y_3021_;
v_a_2868_ = v___y_3020_;
v_a_2869_ = v___y_3023_;
v_a_2870_ = v___y_3026_;
goto _start;
}
v___jp_3030_:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2992_, v___y_3034_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v___x_3048_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3036_, v___y_3034_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; uint8_t v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = lean_nat_dec_lt(v_a_3047_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec(v_a_3047_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_lt(v___y_3042_, v___y_3045_);
lean_dec(v___y_3045_);
if (v___x_3051_ == 0)
{
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3036_);
v___y_2998_ = v___y_3031_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3034_;
v___y_3002_ = v___y_3037_;
v___y_3003_ = v___y_3038_;
v___y_3004_ = v___y_3043_;
v___y_3005_ = v___y_3039_;
v___y_3006_ = v___y_3041_;
v___y_3007_ = v___y_3044_;
goto v___jp_2997_;
}
else
{
lean_del_object(v___x_2995_);
lean_dec(v_c_x3f_2859_);
v___y_3013_ = v___y_3032_;
v___y_3014_ = v___y_3031_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3039_;
v___y_3022_ = v___y_3040_;
v___y_3023_ = v___y_3041_;
v___y_3024_ = v___y_3042_;
v___y_3025_ = v___y_3043_;
v___y_3026_ = v___y_3044_;
goto v___jp_3012_;
}
}
else
{
lean_dec(v___y_3045_);
lean_del_object(v___x_2995_);
lean_dec(v_c_x3f_2859_);
v___y_3013_ = v___y_3032_;
v___y_3014_ = v___y_3031_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3039_;
v___y_3022_ = v___y_3040_;
v___y_3023_ = v___y_3041_;
v___y_3024_ = v___y_3042_;
v___y_3025_ = v___y_3043_;
v___y_3026_ = v___y_3044_;
goto v___jp_3012_;
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec(v_a_3047_);
lean_dec(v___y_3045_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3036_);
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3052_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3048_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3048_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v___y_3045_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3036_);
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_head_2992_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3060_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3046_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3046_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
v___jp_3068_:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = lean_unsigned_to_nat(1u);
v___x_3085_ = lean_nat_dec_lt(v___x_3084_, v___y_3083_);
if (v___x_3085_ == 0)
{
v___y_3031_ = v___y_3069_;
v___y_3032_ = v___y_3070_;
v___y_3033_ = v___y_3071_;
v___y_3034_ = v___y_3072_;
v___y_3035_ = v___y_3073_;
v___y_3036_ = v___y_3074_;
v___y_3037_ = v___y_3075_;
v___y_3038_ = v___y_3076_;
v___y_3039_ = v___y_3077_;
v___y_3040_ = v___y_3078_;
v___y_3041_ = v___y_3079_;
v___y_3042_ = v___y_3080_;
v___y_3043_ = v___y_3081_;
v___y_3044_ = v___y_3082_;
v___y_3045_ = v___y_3083_;
goto v___jp_3030_;
}
else
{
lean_dec(v___y_3083_);
lean_del_object(v___x_2995_);
lean_dec(v_c_x3f_2859_);
v___y_3013_ = v___y_3070_;
v___y_3014_ = v___y_3069_;
v___y_3015_ = v___y_3071_;
v___y_3016_ = v___y_3072_;
v___y_3017_ = v___y_3073_;
v___y_3018_ = v___y_3074_;
v___y_3019_ = v___y_3075_;
v___y_3020_ = v___y_3076_;
v___y_3021_ = v___y_3077_;
v___y_3022_ = v___y_3078_;
v___y_3023_ = v___y_3079_;
v___y_3024_ = v___y_3080_;
v___y_3025_ = v___y_3081_;
v___y_3026_ = v___y_3082_;
goto v___jp_3012_;
}
}
v___jp_3086_:
{
lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3103_ = lean_unsigned_to_nat(1u);
v___x_3104_ = lean_nat_dec_eq(v___y_3098_, v___x_3103_);
if (v___x_3104_ == 0)
{
v___y_3031_ = v___y_3087_;
v___y_3032_ = v___y_3088_;
v___y_3033_ = v___y_3089_;
v___y_3034_ = v___y_3090_;
v___y_3035_ = v___y_3091_;
v___y_3036_ = v___y_3092_;
v___y_3037_ = v___y_3093_;
v___y_3038_ = v___y_3094_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3097_;
v___y_3042_ = v___y_3098_;
v___y_3043_ = v___y_3099_;
v___y_3044_ = v___y_3101_;
v___y_3045_ = v___y_3100_;
goto v___jp_3030_;
}
else
{
if (v___y_3096_ == 0)
{
v___y_3069_ = v___y_3087_;
v___y_3070_ = v___y_3088_;
v___y_3071_ = v___y_3089_;
v___y_3072_ = v___y_3090_;
v___y_3073_ = v___y_3091_;
v___y_3074_ = v___y_3092_;
v___y_3075_ = v___y_3093_;
v___y_3076_ = v___y_3094_;
v___y_3077_ = v___y_3095_;
v___y_3078_ = v___y_3096_;
v___y_3079_ = v___y_3097_;
v___y_3080_ = v___y_3098_;
v___y_3081_ = v___y_3099_;
v___y_3082_ = v___y_3101_;
v___y_3083_ = v___y_3100_;
goto v___jp_3068_;
}
else
{
if (v___y_3102_ == 0)
{
v___y_3031_ = v___y_3087_;
v___y_3032_ = v___y_3088_;
v___y_3033_ = v___y_3089_;
v___y_3034_ = v___y_3090_;
v___y_3035_ = v___y_3091_;
v___y_3036_ = v___y_3092_;
v___y_3037_ = v___y_3093_;
v___y_3038_ = v___y_3094_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3097_;
v___y_3042_ = v___y_3098_;
v___y_3043_ = v___y_3099_;
v___y_3044_ = v___y_3101_;
v___y_3045_ = v___y_3100_;
goto v___jp_3030_;
}
else
{
v___y_3069_ = v___y_3087_;
v___y_3070_ = v___y_3088_;
v___y_3071_ = v___y_3089_;
v___y_3072_ = v___y_3090_;
v___y_3073_ = v___y_3091_;
v___y_3074_ = v___y_3092_;
v___y_3075_ = v___y_3093_;
v___y_3076_ = v___y_3094_;
v___y_3077_ = v___y_3095_;
v___y_3078_ = v___y_3096_;
v___y_3079_ = v___y_3097_;
v___y_3080_ = v___y_3098_;
v___y_3081_ = v___y_3099_;
v___y_3082_ = v___y_3101_;
v___y_3083_ = v___y_3100_;
goto v___jp_3068_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3214_, lean_object* v_c_x3f_3215_, lean_object* v_cs_x27_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3214_, v_c_x3f_3215_, v_cs_x27_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec(v_a_3217_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3229_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3276_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3276_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3276_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_unbox(v_a_3241_);
lean_dec(v_a_3241_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_del_object(v___x_3243_);
v___x_3246_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3263_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3263_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3263_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
uint8_t v___x_3251_; 
v___x_3251_ = lean_unbox(v_a_3247_);
lean_dec(v_a_3247_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; lean_object* v_toGoalState_3253_; lean_object* v_split_3254_; lean_object* v_candidates_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_del_object(v___x_3249_);
v___x_3252_ = lean_st_ref_get(v_a_3229_);
v_toGoalState_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc_ref(v_toGoalState_3253_);
lean_dec(v___x_3252_);
v_split_3254_ = lean_ctor_get(v_toGoalState_3253_, 15);
lean_inc_ref(v_split_3254_);
lean_dec_ref(v_toGoalState_3253_);
v_candidates_3255_ = lean_ctor_get(v_split_3254_, 0);
lean_inc(v_candidates_3255_);
lean_dec_ref(v_split_3254_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_box(0);
v___x_3258_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3255_, v___x_3256_, v___x_3257_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_box(0);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3259_);
v___x_3261_ = v___x_3249_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
v_a_3264_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3246_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3246_);
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
else
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = lean_box(0);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3272_);
v___x_3274_ = v___x_3243_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v_a_3277_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3240_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3240_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec(v_a_3285_);
return v_res_3296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_box(0);
v___x_3305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3306_ = l_Lean_mkConst(v___x_3305_, v___x_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3309_ = l_Lean_Expr_app___override(v___x_3308_, v_c_3307_);
return v___x_3309_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(0);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3320_ = l_Lean_mkConst(v___x_3319_, v___x_3318_);
return v___x_3320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_box(0);
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3328_ = l_Lean_mkConst(v___x_3327_, v___x_3326_);
return v___x_3328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = lean_box(0);
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3336_ = l_Lean_mkConst(v___x_3335_, v___x_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___x_3398_; 
lean_inc_ref(v_c_3337_);
v___x_3398_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3337_, v_a_3345_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3471_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3471_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3471_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3403_ = l_Lean_Expr_cleanupAnnotations(v_a_3399_);
lean_dec(v_a_3399_);
v___x_3404_ = l_Lean_Expr_isApp(v___x_3403_);
if (v___x_3404_ == 0)
{
lean_dec_ref(v___x_3403_);
lean_del_object(v___x_3401_);
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
goto v___jp_3357_;
}
else
{
lean_object* v_arg_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_arg_3405_ = lean_ctor_get(v___x_3403_, 1);
lean_inc_ref(v_arg_3405_);
v___x_3406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3403_);
lean_dec_ref(v___x_3403_);
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3408_ = l_Lean_Expr_isConstOf(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
uint8_t v___x_3409_; 
v___x_3409_ = l_Lean_Expr_isApp(v___x_3406_);
if (v___x_3409_ == 0)
{
lean_dec_ref(v___x_3406_);
lean_dec_ref(v_arg_3405_);
lean_del_object(v___x_3401_);
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
goto v___jp_3357_;
}
else
{
lean_object* v_arg_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_arg_3410_ = lean_ctor_get(v___x_3406_, 1);
lean_inc_ref(v_arg_3410_);
v___x_3411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3406_);
lean_dec_ref(v___x_3406_);
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3413_ = l_Lean_Expr_isConstOf(v___x_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
uint8_t v___x_3414_; 
v___x_3414_ = l_Lean_Expr_isApp(v___x_3411_);
if (v___x_3414_ == 0)
{
lean_dec_ref(v___x_3411_);
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
lean_del_object(v___x_3401_);
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v___x_3415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3417_ = l_Lean_Expr_isConstOf(v___x_3415_, v___x_3416_);
lean_dec_ref(v___x_3415_);
if (v___x_3417_ == 0)
{
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
lean_del_object(v___x_3401_);
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
goto v___jp_3357_;
}
else
{
uint8_t v___x_3418_; 
v___x_3418_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3337_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
v___x_3419_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3337_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3419_);
v___x_3421_ = v___x_3401_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
else
{
lean_object* v___x_3423_; 
lean_del_object(v___x_3401_);
lean_inc_ref(v_c_3337_);
v___x_3423_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3337_, v_a_3338_, v_a_3342_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; uint8_t v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = lean_unbox(v_a_3424_);
lean_dec(v_a_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3436_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3436_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3436_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3432_ = l_Lean_mkApp3(v___x_3431_, v_arg_3410_, v_arg_3405_, v_a_3427_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3432_);
v___x_3434_ = v___x_3429_;
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
else
{
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
return v___x_3426_;
}
}
else
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3447_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3447_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3447_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3443_ = l_Lean_mkApp3(v___x_3442_, v_arg_3410_, v_arg_3405_, v_a_3438_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3443_);
v___x_3445_ = v___x_3440_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
else
{
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
return v___x_3437_;
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_c_3337_);
v_a_3448_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3423_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3423_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3456_; 
lean_dec_ref(v___x_3411_);
lean_del_object(v___x_3401_);
v___x_3456_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3466_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3466_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3466_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3462_ = l_Lean_mkApp3(v___x_3461_, v_arg_3410_, v_arg_3405_, v_a_3457_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3462_);
v___x_3464_ = v___x_3459_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
else
{
lean_dec_ref(v_arg_3410_);
lean_dec_ref(v_arg_3405_);
return v___x_3456_;
}
}
}
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
lean_dec_ref(v___x_3406_);
lean_dec_ref(v_c_3337_);
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3405_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3467_);
v___x_3469_ = v___x_3401_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3337_);
return v___x_3398_;
}
v___jp_3349_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3350_ = lean_unsigned_to_nat(1u);
v___x_3351_ = l_Lean_Expr_getAppNumArgs(v_c_3337_);
v___x_3352_ = lean_nat_sub(v___x_3351_, v___x_3350_);
lean_dec(v___x_3351_);
v___x_3353_ = lean_nat_sub(v___x_3352_, v___x_3350_);
lean_dec(v___x_3352_);
v___x_3354_ = l_Lean_Expr_getRevArg_x21(v_c_3337_, v___x_3353_);
lean_dec_ref(v_c_3337_);
v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3354_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
v___jp_3357_:
{
uint8_t v___x_3368_; 
v___x_3368_ = l_Lean_Meta_Grind_isIte(v_c_3337_);
if (v___x_3368_ == 0)
{
uint8_t v___x_3369_; 
v___x_3369_ = l_Lean_Meta_Grind_isDIte(v_c_3337_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_inc_ref(v_c_3337_);
v___x_3370_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3337_, v___y_3358_, v___y_3362_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3389_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3389_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3389_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_unbox(v_a_3371_);
lean_dec(v_a_3371_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3377_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v_c_3337_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_c_3337_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
else
{
lean_object* v___x_3379_; 
lean_del_object(v___x_3373_);
lean_inc_ref(v_c_3337_);
v___x_3379_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3337_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3388_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3388_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3388_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3384_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3337_, v_a_3380_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3384_);
v___x_3386_ = v___x_3382_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
else
{
lean_dec_ref(v_c_3337_);
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref(v_c_3337_);
v_a_3390_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3370_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3370_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
goto v___jp_3349_;
}
}
else
{
goto v___jp_3349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec(v_a_3473_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3485_, lean_object* v_major_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3487_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; uint8_t v_trace_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v_trace_3496_ = lean_ctor_get_uint8(v_a_3495_, sizeof(void*)*18);
lean_dec(v_a_3495_);
if (v_trace_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Meta_Grind_cases(v_mvarId_3485_, v_major_3486_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; 
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
lean_inc_ref(v_major_3486_);
v___x_3498_ = lean_infer_type(v_major_3486_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = l_Lean_Meta_whnfD(v_a_3499_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Expr_getAppFn(v_a_3501_);
lean_dec(v_a_3501_);
if (lean_obj_tag(v___x_3502_) == 4)
{
lean_object* v_declName_3503_; lean_object* v___x_3504_; 
v_declName_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_declName_3503_);
lean_dec_ref_known(v___x_3502_, 2);
v___x_3504_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3503_, v_a_3488_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3504_, 1);
v___x_3505_ = l_Lean_Meta_Grind_cases(v_mvarId_3485_, v_major_3486_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
return v___x_3505_;
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec_ref(v_major_3486_);
lean_dec(v_mvarId_3485_);
v_a_3506_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3504_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3504_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v___x_3514_; 
lean_dec_ref(v___x_3502_);
v___x_3514_ = l_Lean_Meta_Grind_cases(v_mvarId_3485_, v_major_3486_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
return v___x_3514_;
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec_ref(v_major_3486_);
lean_dec(v_mvarId_3485_);
v_a_3515_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3500_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3500_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v_major_3486_);
lean_dec(v_mvarId_3485_);
v_a_3523_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3498_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3498_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
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
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v_major_3486_);
lean_dec(v_mvarId_3485_);
v_a_3531_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3494_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3494_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3539_, lean_object* v_major_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3539_, v_major_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3549_, lean_object* v_major_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3549_, v_major_3550_, v_a_3553_, v_a_3554_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3563_, lean_object* v_major_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3563_, v_major_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec(v_a_3565_);
return v_res_3576_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3577_){
_start:
{
uint64_t v_anchor_3578_; 
v_anchor_3578_ = lean_ctor_get_uint64(v_e_3577_, sizeof(void*)*3);
return v_anchor_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3579_){
_start:
{
uint64_t v_res_3580_; lean_object* v_r_3581_; 
v_res_3580_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3579_);
lean_dec_ref(v_e_3579_);
v_r_3581_ = lean_box_uint64(v_res_3580_);
return v_r_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3584_, lean_object* v_x_3585_){
_start:
{
if (lean_obj_tag(v_x_3585_) == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_box(0);
return v___x_3586_;
}
else
{
lean_object* v_key_3587_; lean_object* v_value_3588_; lean_object* v_tail_3589_; uint64_t v___x_3590_; uint8_t v___x_3591_; 
v_key_3587_ = lean_ctor_get(v_x_3585_, 0);
v_value_3588_ = lean_ctor_get(v_x_3585_, 1);
v_tail_3589_ = lean_ctor_get(v_x_3585_, 2);
v___x_3590_ = lean_unbox_uint64(v_key_3587_);
v___x_3591_ = lean_uint64_dec_eq(v___x_3590_, v_a_3584_);
if (v___x_3591_ == 0)
{
v_x_3585_ = v_tail_3589_;
goto _start;
}
else
{
lean_object* v___x_3593_; 
lean_inc(v_value_3588_);
v___x_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3593_, 0, v_value_3588_);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3594_, lean_object* v_x_3595_){
_start:
{
uint64_t v_a_boxed_3596_; lean_object* v_res_3597_; 
v_a_boxed_3596_ = lean_unbox_uint64(v_a_3594_);
lean_dec_ref(v_a_3594_);
v_res_3597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3596_, v_x_3595_);
lean_dec(v_x_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3598_, uint64_t v_a_3599_){
_start:
{
lean_object* v_buckets_3600_; lean_object* v___x_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v_fold_3604_; uint64_t v___x_3605_; uint64_t v___x_3606_; uint64_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_buckets_3600_ = lean_ctor_get(v_m_3598_, 1);
v___x_3601_ = lean_array_get_size(v_buckets_3600_);
v___x_3602_ = 32ULL;
v___x_3603_ = lean_uint64_shift_right(v_a_3599_, v___x_3602_);
v_fold_3604_ = lean_uint64_xor(v_a_3599_, v___x_3603_);
v___x_3605_ = 16ULL;
v___x_3606_ = lean_uint64_shift_right(v_fold_3604_, v___x_3605_);
v___x_3607_ = lean_uint64_xor(v_fold_3604_, v___x_3606_);
v___x_3608_ = lean_uint64_to_usize(v___x_3607_);
v___x_3609_ = lean_usize_of_nat(v___x_3601_);
v___x_3610_ = ((size_t)1ULL);
v___x_3611_ = lean_usize_sub(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_usize_land(v___x_3608_, v___x_3611_);
v___x_3613_ = lean_array_uget_borrowed(v_buckets_3600_, v___x_3612_);
v___x_3614_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3599_, v___x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3615_, lean_object* v_a_3616_){
_start:
{
uint64_t v_a_boxed_3617_; lean_object* v_res_3618_; 
v_a_boxed_3617_ = lean_unbox_uint64(v_a_3616_);
lean_dec_ref(v_a_3616_);
v_res_3618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3615_, v_a_boxed_3617_);
lean_dec_ref(v_m_3615_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
if (lean_obj_tag(v_x_3620_) == 0)
{
return v_x_3619_;
}
else
{
lean_object* v_key_3621_; lean_object* v_value_3622_; lean_object* v_tail_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3647_; 
v_key_3621_ = lean_ctor_get(v_x_3620_, 0);
v_value_3622_ = lean_ctor_get(v_x_3620_, 1);
v_tail_3623_ = lean_ctor_get(v_x_3620_, 2);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_x_3620_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3625_ = v_x_3620_;
v_isShared_3626_ = v_isSharedCheck_3647_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_tail_3623_);
lean_inc(v_value_3622_);
lean_inc(v_key_3621_);
lean_dec(v_x_3620_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3647_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; uint64_t v___x_3628_; uint64_t v___x_3629_; uint64_t v___x_3630_; uint64_t v___x_3631_; uint64_t v_fold_3632_; uint64_t v___x_3633_; uint64_t v___x_3634_; uint64_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3627_ = lean_array_get_size(v_x_3619_);
v___x_3628_ = 32ULL;
v___x_3629_ = lean_unbox_uint64(v_key_3621_);
v___x_3630_ = lean_uint64_shift_right(v___x_3629_, v___x_3628_);
v___x_3631_ = lean_unbox_uint64(v_key_3621_);
v_fold_3632_ = lean_uint64_xor(v___x_3631_, v___x_3630_);
v___x_3633_ = 16ULL;
v___x_3634_ = lean_uint64_shift_right(v_fold_3632_, v___x_3633_);
v___x_3635_ = lean_uint64_xor(v_fold_3632_, v___x_3634_);
v___x_3636_ = lean_uint64_to_usize(v___x_3635_);
v___x_3637_ = lean_usize_of_nat(v___x_3627_);
v___x_3638_ = ((size_t)1ULL);
v___x_3639_ = lean_usize_sub(v___x_3637_, v___x_3638_);
v___x_3640_ = lean_usize_land(v___x_3636_, v___x_3639_);
v___x_3641_ = lean_array_uget_borrowed(v_x_3619_, v___x_3640_);
lean_inc(v___x_3641_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 2, v___x_3641_);
v___x_3643_ = v___x_3625_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_key_3621_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_value_3622_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_array_uset(v_x_3619_, v___x_3640_, v___x_3643_);
v_x_3619_ = v___x_3644_;
v_x_3620_ = v_tail_3623_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3648_, lean_object* v_source_3649_, lean_object* v_target_3650_){
_start:
{
lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = lean_array_get_size(v_source_3649_);
v___x_3652_ = lean_nat_dec_lt(v_i_3648_, v___x_3651_);
if (v___x_3652_ == 0)
{
lean_dec_ref(v_source_3649_);
lean_dec(v_i_3648_);
return v_target_3650_;
}
else
{
lean_object* v_es_3653_; lean_object* v___x_3654_; lean_object* v_source_3655_; lean_object* v_target_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_es_3653_ = lean_array_fget(v_source_3649_, v_i_3648_);
v___x_3654_ = lean_box(0);
v_source_3655_ = lean_array_fset(v_source_3649_, v_i_3648_, v___x_3654_);
v_target_3656_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3650_, v_es_3653_);
v___x_3657_ = lean_unsigned_to_nat(1u);
v___x_3658_ = lean_nat_add(v_i_3648_, v___x_3657_);
lean_dec(v_i_3648_);
v_i_3648_ = v___x_3658_;
v_source_3649_ = v_source_3655_;
v_target_3650_ = v_target_3656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3660_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v_nbuckets_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3661_ = lean_array_get_size(v_data_3660_);
v___x_3662_ = lean_unsigned_to_nat(2u);
v_nbuckets_3663_ = lean_nat_mul(v___x_3661_, v___x_3662_);
v___x_3664_ = lean_unsigned_to_nat(0u);
v___x_3665_ = lean_box(0);
v___x_3666_ = lean_mk_array(v_nbuckets_3663_, v___x_3665_);
v___x_3667_ = lean_array_propagate_mark(v_data_3660_, v___x_3666_);
v___x_3668_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3664_, v_data_3660_, v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3669_, lean_object* v_b_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 0)
{
lean_dec(v_b_3670_);
return v_x_3671_;
}
else
{
lean_object* v_key_3672_; lean_object* v_value_3673_; lean_object* v_tail_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3688_; 
v_key_3672_ = lean_ctor_get(v_x_3671_, 0);
v_value_3673_ = lean_ctor_get(v_x_3671_, 1);
v_tail_3674_ = lean_ctor_get(v_x_3671_, 2);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_x_3671_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3676_ = v_x_3671_;
v_isShared_3677_ = v_isSharedCheck_3688_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_tail_3674_);
lean_inc(v_value_3673_);
lean_inc(v_key_3672_);
lean_dec(v_x_3671_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3688_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
uint64_t v___x_3678_; uint8_t v___x_3679_; 
v___x_3678_ = lean_unbox_uint64(v_key_3672_);
v___x_3679_ = lean_uint64_dec_eq(v___x_3678_, v_a_3669_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3680_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3669_, v_b_3670_, v_tail_3674_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 2, v___x_3680_);
v___x_3682_ = v___x_3676_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_key_3672_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_value_3673_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
lean_dec(v_value_3673_);
lean_dec(v_key_3672_);
v___x_3684_ = lean_box_uint64(v_a_3669_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 1, v_b_3670_);
lean_ctor_set(v___x_3676_, 0, v___x_3684_);
v___x_3686_ = v___x_3676_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_b_3670_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_tail_3674_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3689_, lean_object* v_b_3690_, lean_object* v_x_3691_){
_start:
{
uint64_t v_a_boxed_3692_; lean_object* v_res_3693_; 
v_a_boxed_3692_ = lean_unbox_uint64(v_a_3689_);
lean_dec_ref(v_a_3689_);
v_res_3693_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3692_, v_b_3690_, v_x_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3695_) == 0)
{
uint8_t v___x_3696_; 
v___x_3696_ = 0;
return v___x_3696_;
}
else
{
lean_object* v_key_3697_; lean_object* v_tail_3698_; uint64_t v___x_3699_; uint8_t v___x_3700_; 
v_key_3697_ = lean_ctor_get(v_x_3695_, 0);
v_tail_3698_ = lean_ctor_get(v_x_3695_, 2);
v___x_3699_ = lean_unbox_uint64(v_key_3697_);
v___x_3700_ = lean_uint64_dec_eq(v___x_3699_, v_a_3694_);
if (v___x_3700_ == 0)
{
v_x_3695_ = v_tail_3698_;
goto _start;
}
else
{
return v___x_3700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3702_, lean_object* v_x_3703_){
_start:
{
uint64_t v_a_boxed_3704_; uint8_t v_res_3705_; lean_object* v_r_3706_; 
v_a_boxed_3704_ = lean_unbox_uint64(v_a_3702_);
lean_dec_ref(v_a_3702_);
v_res_3705_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3704_, v_x_3703_);
lean_dec(v_x_3703_);
v_r_3706_ = lean_box(v_res_3705_);
return v_r_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3707_, uint64_t v_a_3708_, lean_object* v_b_3709_){
_start:
{
lean_object* v_size_3710_; lean_object* v_buckets_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3754_; 
v_size_3710_ = lean_ctor_get(v_m_3707_, 0);
v_buckets_3711_ = lean_ctor_get(v_m_3707_, 1);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_m_3707_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3713_ = v_m_3707_;
v_isShared_3714_ = v_isSharedCheck_3754_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_buckets_3711_);
lean_inc(v_size_3710_);
lean_dec(v_m_3707_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3754_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; uint64_t v___x_3716_; uint64_t v___x_3717_; uint64_t v_fold_3718_; uint64_t v___x_3719_; uint64_t v___x_3720_; uint64_t v___x_3721_; size_t v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; lean_object* v_bkt_3727_; uint8_t v___x_3728_; 
v___x_3715_ = lean_array_get_size(v_buckets_3711_);
v___x_3716_ = 32ULL;
v___x_3717_ = lean_uint64_shift_right(v_a_3708_, v___x_3716_);
v_fold_3718_ = lean_uint64_xor(v_a_3708_, v___x_3717_);
v___x_3719_ = 16ULL;
v___x_3720_ = lean_uint64_shift_right(v_fold_3718_, v___x_3719_);
v___x_3721_ = lean_uint64_xor(v_fold_3718_, v___x_3720_);
v___x_3722_ = lean_uint64_to_usize(v___x_3721_);
v___x_3723_ = lean_usize_of_nat(v___x_3715_);
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_sub(v___x_3723_, v___x_3724_);
v___x_3726_ = lean_usize_land(v___x_3722_, v___x_3725_);
v_bkt_3727_ = lean_array_uget_borrowed(v_buckets_3711_, v___x_3726_);
v___x_3728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3708_, v_bkt_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; lean_object* v_size_x27_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v_buckets_x27_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3729_ = lean_unsigned_to_nat(1u);
v_size_x27_3730_ = lean_nat_add(v_size_3710_, v___x_3729_);
lean_dec(v_size_3710_);
v___x_3731_ = lean_box_uint64(v_a_3708_);
lean_inc(v_bkt_3727_);
v___x_3732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v_b_3709_);
lean_ctor_set(v___x_3732_, 2, v_bkt_3727_);
v_buckets_x27_3733_ = lean_array_uset(v_buckets_3711_, v___x_3726_, v___x_3732_);
v___x_3734_ = lean_unsigned_to_nat(4u);
v___x_3735_ = lean_nat_mul(v_size_x27_3730_, v___x_3734_);
v___x_3736_ = lean_unsigned_to_nat(3u);
v___x_3737_ = lean_nat_div(v___x_3735_, v___x_3736_);
lean_dec(v___x_3735_);
v___x_3738_ = lean_array_get_size(v_buckets_x27_3733_);
v___x_3739_ = lean_nat_dec_le(v___x_3737_, v___x_3738_);
lean_dec(v___x_3737_);
if (v___x_3739_ == 0)
{
lean_object* v_val_3740_; lean_object* v___x_3742_; 
v_val_3740_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3733_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v_val_3740_);
lean_ctor_set(v___x_3713_, 0, v_size_x27_3730_);
v___x_3742_ = v___x_3713_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_size_x27_3730_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_val_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
else
{
lean_object* v___x_3745_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v_buckets_x27_3733_);
lean_ctor_set(v___x_3713_, 0, v_size_x27_3730_);
v___x_3745_ = v___x_3713_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_size_x27_3730_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_buckets_x27_3733_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
lean_object* v___x_3747_; lean_object* v_buckets_x27_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
lean_inc(v_bkt_3727_);
v___x_3747_ = lean_box(0);
v_buckets_x27_3748_ = lean_array_uset(v_buckets_3711_, v___x_3726_, v___x_3747_);
v___x_3749_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3708_, v_b_3709_, v_bkt_3727_);
v___x_3750_ = lean_array_uset(v_buckets_x27_3748_, v___x_3726_, v___x_3749_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3750_);
v___x_3752_ = v___x_3713_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_size_3710_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3755_, lean_object* v_a_3756_, lean_object* v_b_3757_){
_start:
{
uint64_t v_a_boxed_3758_; lean_object* v_res_3759_; 
v_a_boxed_3758_ = lean_unbox_uint64(v_a_3756_);
lean_dec_ref(v_a_3756_);
v_res_3759_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3755_, v_a_boxed_3758_, v_b_3757_);
return v_res_3759_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_box(0);
v___x_3761_ = lean_unsigned_to_nat(16u);
v___x_3762_ = lean_mk_array(v___x_3761_, v___x_3760_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v_found_3765_; 
v___x_3763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3764_ = lean_unsigned_to_nat(0u);
v_found_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3765_, 0, v___x_3764_);
lean_ctor_set(v_found_3765_, 1, v___x_3763_);
return v_found_3765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v_found_3766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3767_ = lean_box(0);
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
lean_ctor_set(v___x_3768_, 1, v_found_3766_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3769_, lean_object* v_numDigits_3770_, lean_object* v_es_3771_, lean_object* v_as_3772_, size_t v_sz_3773_, size_t v_i_3774_, lean_object* v_b_3775_){
_start:
{
lean_object* v_a_3777_; uint8_t v___x_3781_; 
v___x_3781_ = lean_usize_dec_lt(v_i_3774_, v_sz_3773_);
if (v___x_3781_ == 0)
{
return v_b_3775_;
}
else
{
lean_object* v_snd_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3816_; 
v_snd_3782_ = lean_ctor_get(v_b_3775_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_b_3775_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v_b_3775_, 0);
lean_dec(v_unused_3817_);
v___x_3784_ = v_b_3775_;
v_isShared_3785_ = v_isSharedCheck_3816_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_snd_3782_);
lean_dec(v_b_3775_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3816_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v_a_3786_; uint64_t v_anchor_3787_; lean_object* v___x_3788_; uint64_t v___x_3789_; uint64_t v___x_3790_; lean_object* v___x_3791_; 
v_a_3786_ = lean_array_uget_borrowed(v_as_3772_, v_i_3774_);
v_anchor_3787_ = lean_ctor_get_uint64(v_a_3786_, sizeof(void*)*3);
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_uint64_of_nat(v_shift_3769_);
v___x_3790_ = lean_uint64_shift_right(v_anchor_3787_, v___x_3789_);
v___x_3791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3782_, v___x_3790_);
if (lean_obj_tag(v___x_3791_) == 1)
{
lean_object* v_val_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3810_; 
v_val_3792_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3794_ = v___x_3791_;
v_isShared_3795_ = v_isSharedCheck_3810_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_val_3792_);
lean_dec(v___x_3791_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3810_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
uint64_t v___x_3796_; uint8_t v___x_3797_; 
v___x_3796_ = lean_unbox_uint64(v_val_3792_);
lean_dec(v_val_3792_);
v___x_3797_ = lean_uint64_dec_eq(v___x_3796_, v_anchor_3787_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3798_ = lean_unsigned_to_nat(1u);
v___x_3799_ = lean_nat_add(v_numDigits_3770_, v___x_3798_);
v___x_3800_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3771_, v___x_3799_);
lean_dec(v___x_3799_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3800_);
v___x_3802_ = v___x_3794_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3804_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3802_);
v___x_3804_ = v___x_3784_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_snd_3782_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
else
{
lean_object* v___x_3808_; 
lean_del_object(v___x_3794_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3788_);
v___x_3808_ = v___x_3784_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_snd_3782_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
v_a_3777_ = v___x_3808_;
goto v___jp_3776_;
}
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
lean_dec(v___x_3791_);
v___x_3811_ = lean_box_uint64(v_anchor_3787_);
v___x_3812_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3782_, v___x_3790_, v___x_3811_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v___x_3812_);
lean_ctor_set(v___x_3784_, 0, v___x_3788_);
v___x_3814_ = v___x_3784_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
v_a_3777_ = v___x_3814_;
goto v___jp_3776_;
}
}
}
}
v___jp_3776_:
{
size_t v___x_3778_; size_t v___x_3779_; 
v___x_3778_ = ((size_t)1ULL);
v___x_3779_ = lean_usize_add(v_i_3774_, v___x_3778_);
v_i_3774_ = v___x_3779_;
v_b_3775_ = v_a_3777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3818_, lean_object* v_numDigits_3819_){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3820_ = lean_unsigned_to_nat(4u);
v___x_3821_ = lean_nat_mul(v___x_3820_, v_numDigits_3819_);
v___x_3822_ = lean_unsigned_to_nat(64u);
v___x_3823_ = lean_nat_dec_lt(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_dec(v___x_3821_);
lean_inc(v_numDigits_3819_);
return v_numDigits_3819_;
}
else
{
lean_object* v_shift_3824_; lean_object* v___x_3825_; size_t v_sz_3826_; size_t v___x_3827_; lean_object* v___x_3828_; lean_object* v_fst_3829_; 
v_shift_3824_ = lean_nat_sub(v___x_3822_, v___x_3821_);
lean_dec(v___x_3821_);
v___x_3825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3826_ = lean_array_size(v_es_3818_);
v___x_3827_ = ((size_t)0ULL);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3824_, v_numDigits_3819_, v_es_3818_, v_es_3818_, v_sz_3826_, v___x_3827_, v___x_3825_);
lean_dec(v_shift_3824_);
v_fst_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_fst_3829_);
lean_dec_ref(v___x_3828_);
if (lean_obj_tag(v_fst_3829_) == 0)
{
lean_inc(v_numDigits_3819_);
return v_numDigits_3819_;
}
else
{
lean_object* v_val_3830_; 
v_val_3830_ = lean_ctor_get(v_fst_3829_, 0);
lean_inc(v_val_3830_);
lean_dec_ref_known(v_fst_3829_, 1);
return v_val_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3831_, lean_object* v_numDigits_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3831_, v_numDigits_3832_);
lean_dec(v_numDigits_3832_);
lean_dec_ref(v_es_3831_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3834_, lean_object* v_numDigits_3835_, lean_object* v_es_3836_, lean_object* v_as_3837_, lean_object* v_sz_3838_, lean_object* v_i_3839_, lean_object* v_b_3840_){
_start:
{
size_t v_sz_boxed_3841_; size_t v_i_boxed_3842_; lean_object* v_res_3843_; 
v_sz_boxed_3841_ = lean_unbox_usize(v_sz_3838_);
lean_dec(v_sz_3838_);
v_i_boxed_3842_ = lean_unbox_usize(v_i_3839_);
lean_dec(v_i_3839_);
v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3834_, v_numDigits_3835_, v_es_3836_, v_as_3837_, v_sz_boxed_3841_, v_i_boxed_3842_, v_b_3840_);
lean_dec_ref(v_as_3837_);
lean_dec_ref(v_es_3836_);
lean_dec(v_numDigits_3835_);
lean_dec(v_shift_3834_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3844_){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_unsigned_to_nat(4u);
v___x_3846_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3844_, v___x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3847_);
lean_dec_ref(v_es_3847_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3849_, lean_object* v_as_3850_, size_t v_i_3851_, size_t v_stop_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_a_3866_; uint8_t v___x_3870_; 
v___x_3870_ = lean_usize_dec_eq(v_i_3851_, v_stop_3852_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v_e_3872_; lean_object* v___x_3873_; 
v___x_3871_ = lean_array_uget_borrowed(v_as_3850_, v_i_3851_);
v_e_3872_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3871_);
v___x_3873_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3871_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
lean_inc(v___x_3871_);
v___x_3875_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3871_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
if (lean_obj_tag(v_a_3876_) == 2)
{
lean_object* v_numCases_3877_; uint8_t v_isRec_3878_; lean_object* v___x_3879_; 
v_numCases_3877_ = lean_ctor_get(v_a_3876_, 0);
lean_inc(v_numCases_3877_);
v_isRec_3878_ = lean_ctor_get_uint8(v_a_3876_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3876_, 1);
lean_inc_ref(v_filter_3849_);
lean_inc(v___y_3863_);
lean_inc_ref(v___y_3862_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc(v___y_3854_);
lean_inc_ref(v_e_3872_);
v___x_3879_ = lean_apply_12(v_filter_3849_, v_e_3872_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, lean_box(0));
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; uint8_t v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = lean_unbox(v_a_3880_);
lean_dec(v_a_3880_);
if (v___x_3881_ == 0)
{
lean_dec(v_numCases_3877_);
lean_dec(v_a_3874_);
lean_dec_ref(v_e_3872_);
v_a_3866_ = v_b_3853_;
goto v___jp_3865_;
}
else
{
lean_object* v___x_3882_; uint64_t v___x_3883_; lean_object* v___x_3884_; 
lean_inc(v___x_3871_);
v___x_3882_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3882_, 0, v___x_3871_);
lean_ctor_set(v___x_3882_, 1, v_numCases_3877_);
lean_ctor_set(v___x_3882_, 2, v_e_3872_);
lean_ctor_set_uint8(v___x_3882_, sizeof(void*)*3 + 8, v_isRec_3878_);
v___x_3883_ = lean_unbox_uint64(v_a_3874_);
lean_dec(v_a_3874_);
lean_ctor_set_uint64(v___x_3882_, sizeof(void*)*3, v___x_3883_);
v___x_3884_ = lean_array_push(v_b_3853_, v___x_3882_);
v_a_3866_ = v___x_3884_;
goto v___jp_3865_;
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec(v_numCases_3877_);
lean_dec(v_a_3874_);
lean_dec_ref(v_e_3872_);
lean_dec_ref(v_b_3853_);
lean_dec_ref(v_filter_3849_);
v_a_3885_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3879_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3879_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
lean_dec(v_a_3876_);
lean_dec(v_a_3874_);
lean_dec_ref(v_e_3872_);
v_a_3866_ = v_b_3853_;
goto v___jp_3865_;
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v_a_3874_);
lean_dec_ref(v_e_3872_);
lean_dec_ref(v_b_3853_);
lean_dec_ref(v_filter_3849_);
v_a_3893_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3875_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3875_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v_e_3872_);
lean_dec_ref(v_b_3853_);
lean_dec_ref(v_filter_3849_);
v_a_3901_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3873_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3873_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_object* v___x_3909_; 
lean_dec_ref(v_filter_3849_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v_b_3853_);
return v___x_3909_;
}
v___jp_3865_:
{
size_t v___x_3867_; size_t v___x_3868_; 
v___x_3867_ = ((size_t)1ULL);
v___x_3868_ = lean_usize_add(v_i_3851_, v___x_3867_);
v_i_3851_ = v___x_3868_;
v_b_3853_ = v_a_3866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3910_, lean_object* v_as_3911_, lean_object* v_i_3912_, lean_object* v_stop_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
size_t v_i_boxed_3926_; size_t v_stop_boxed_3927_; lean_object* v_res_3928_; 
v_i_boxed_3926_ = lean_unbox_usize(v_i_3912_);
lean_dec(v_i_3912_);
v_stop_boxed_3927_ = lean_unbox_usize(v_stop_3913_);
lean_dec(v_stop_3913_);
v_res_3928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3910_, v_as_3911_, v_i_boxed_3926_, v_stop_boxed_3927_, v_b_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v_as_3911_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3931_, lean_object* v_as_3932_, lean_object* v_start_3933_, lean_object* v_stop_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3947_ = lean_nat_dec_lt(v_start_3933_, v_stop_3934_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
lean_dec_ref(v_filter_3931_);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
return v___x_3948_;
}
else
{
lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3949_ = lean_array_get_size(v_as_3932_);
v___x_3950_ = lean_nat_dec_le(v_stop_3934_, v___x_3949_);
if (v___x_3950_ == 0)
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_nat_dec_lt(v_start_3933_, v___x_3949_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
lean_dec_ref(v_filter_3931_);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3946_);
return v___x_3952_;
}
else
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = lean_usize_of_nat(v_start_3933_);
v___x_3954_ = lean_usize_of_nat(v___x_3949_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3931_, v_as_3932_, v___x_3953_, v___x_3954_, v___x_3946_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3955_;
}
}
else
{
size_t v___x_3956_; size_t v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_usize_of_nat(v_start_3933_);
v___x_3957_ = lean_usize_of_nat(v_stop_3934_);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3931_, v_as_3932_, v___x_3956_, v___x_3957_, v___x_3946_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3959_, lean_object* v_as_3960_, lean_object* v_start_3961_, lean_object* v_stop_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3959_, v_as_3960_, v_start_3961_, v_stop_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec(v_stop_3962_);
lean_dec(v_start_3961_);
lean_dec_ref(v_as_3960_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3975_, lean_object* v_candidates_x3f_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_candidates_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; 
if (lean_obj_tag(v_candidates_x3f_3976_) == 0)
{
lean_object* v___x_4022_; lean_object* v_toGoalState_4023_; lean_object* v_split_4024_; lean_object* v_candidates_4025_; 
v___x_4022_ = lean_st_ref_get(v_a_3977_);
v_toGoalState_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_ref(v_toGoalState_4023_);
lean_dec(v___x_4022_);
v_split_4024_ = lean_ctor_get(v_toGoalState_4023_, 15);
lean_inc_ref(v_split_4024_);
lean_dec_ref(v_toGoalState_4023_);
v_candidates_4025_ = lean_ctor_get(v_split_4024_, 0);
lean_inc(v_candidates_4025_);
lean_dec_ref(v_split_4024_);
v_candidates_3989_ = v_candidates_4025_;
v___y_3990_ = v_a_3977_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
goto v___jp_3988_;
}
else
{
lean_object* v_val_4026_; 
v_val_4026_ = lean_ctor_get(v_candidates_x3f_3976_, 0);
lean_inc(v_val_4026_);
lean_dec_ref_known(v_candidates_x3f_3976_, 1);
v_candidates_3989_ = v_val_4026_;
v___y_3990_ = v_a_3977_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
goto v___jp_3988_;
}
v___jp_3988_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4000_ = lean_array_mk(v_candidates_3989_);
v___x_4001_ = lean_unsigned_to_nat(0u);
v___x_4002_ = lean_array_get_size(v___x_4000_);
v___x_4003_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3975_, v___x_4000_, v___x_4001_, v___x_4002_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec_ref(v___x_4000_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4013_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4006_ = v___x_4003_;
v_isShared_4007_ = v_isSharedCheck_4013_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4013_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4008_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4004_);
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v_a_4004_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4009_);
v___x_4011_ = v___x_4006_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
v_a_4014_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_4003_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4003_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4027_, lean_object* v_candidates_x3f_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4027_, v_candidates_x3f_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
lean_dec(v_a_4029_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4041_, lean_object* v_m_4042_, uint64_t v_a_4043_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4042_, v_a_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4045_, lean_object* v_m_4046_, lean_object* v_a_4047_){
_start:
{
uint64_t v_a_boxed_4048_; lean_object* v_res_4049_; 
v_a_boxed_4048_ = lean_unbox_uint64(v_a_4047_);
lean_dec_ref(v_a_4047_);
v_res_4049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4045_, v_m_4046_, v_a_boxed_4048_);
lean_dec_ref(v_m_4046_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4050_, lean_object* v_m_4051_, uint64_t v_a_4052_, lean_object* v_b_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4051_, v_a_4052_, v_b_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4055_, lean_object* v_m_4056_, lean_object* v_a_4057_, lean_object* v_b_4058_){
_start:
{
uint64_t v_a_boxed_4059_; lean_object* v_res_4060_; 
v_a_boxed_4059_ = lean_unbox_uint64(v_a_4057_);
lean_dec_ref(v_a_4057_);
v_res_4060_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4055_, v_m_4056_, v_a_boxed_4059_, v_b_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4061_, uint64_t v_a_4062_, lean_object* v_x_4063_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4062_, v_x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4065_, lean_object* v_a_4066_, lean_object* v_x_4067_){
_start:
{
uint64_t v_a_boxed_4068_; lean_object* v_res_4069_; 
v_a_boxed_4068_ = lean_unbox_uint64(v_a_4066_);
lean_dec_ref(v_a_4066_);
v_res_4069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4065_, v_a_boxed_4068_, v_x_4067_);
lean_dec(v_x_4067_);
return v_res_4069_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4070_, uint64_t v_a_4071_, lean_object* v_x_4072_){
_start:
{
uint8_t v___x_4073_; 
v___x_4073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4071_, v_x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4074_, lean_object* v_a_4075_, lean_object* v_x_4076_){
_start:
{
uint64_t v_a_boxed_4077_; uint8_t v_res_4078_; lean_object* v_r_4079_; 
v_a_boxed_4077_ = lean_unbox_uint64(v_a_4075_);
lean_dec_ref(v_a_4075_);
v_res_4078_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4074_, v_a_boxed_4077_, v_x_4076_);
lean_dec(v_x_4076_);
v_r_4079_ = lean_box(v_res_4078_);
return v_r_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4080_, lean_object* v_data_4081_){
_start:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4083_, uint64_t v_a_4084_, lean_object* v_b_4085_, lean_object* v_x_4086_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4084_, v_b_4085_, v_x_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4088_, lean_object* v_a_4089_, lean_object* v_b_4090_, lean_object* v_x_4091_){
_start:
{
uint64_t v_a_boxed_4092_; lean_object* v_res_4093_; 
v_a_boxed_4092_ = lean_unbox_uint64(v_a_4089_);
lean_dec_ref(v_a_4089_);
v_res_4093_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4088_, v_a_boxed_4092_, v_b_4090_, v_x_4091_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4094_, lean_object* v_i_4095_, lean_object* v_source_4096_, lean_object* v_target_4097_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4095_, v_source_4096_, v_target_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4099_, lean_object* v_x_4100_, lean_object* v_x_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4100_, v_x_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = 1;
v___x_4116_ = lean_box(v___x_4115_);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v_x_4118_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4131_, uint64_t v_a_4132_, lean_object* v_c_4133_, lean_object* v_numDigits_4134_, lean_object* v_as_4135_, size_t v_sz_4136_, size_t v_i_4137_, lean_object* v_b_4138_){
_start:
{
lean_object* v_a_4141_; uint8_t v___x_4145_; 
v___x_4145_ = lean_usize_dec_lt(v_i_4137_, v_sz_4136_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; 
lean_dec(v_numDigits_4134_);
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_b_4138_);
return v___x_4146_;
}
else
{
lean_object* v_snd_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4173_; 
v_snd_4147_ = lean_ctor_get(v_b_4138_, 1);
v_isSharedCheck_4173_ = !lean_is_exclusive(v_b_4138_);
if (v_isSharedCheck_4173_ == 0)
{
lean_object* v_unused_4174_; 
v_unused_4174_ = lean_ctor_get(v_b_4138_, 0);
lean_dec(v_unused_4174_);
v___x_4149_ = v_b_4138_;
v_isShared_4150_ = v_isSharedCheck_4173_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_snd_4147_);
lean_dec(v_b_4138_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4173_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v_a_4151_; lean_object* v_c_4152_; uint64_t v_anchor_4153_; lean_object* v___x_4154_; uint64_t v___x_4155_; uint64_t v___x_4156_; uint8_t v___x_4157_; 
v_a_4151_ = lean_array_uget_borrowed(v_as_4135_, v_i_4137_);
v_c_4152_ = lean_ctor_get(v_a_4151_, 0);
v_anchor_4153_ = lean_ctor_get_uint64(v_a_4151_, sizeof(void*)*3);
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_uint64_shift_right(v_anchor_4153_, v___x_4131_);
v___x_4156_ = lean_uint64_shift_right(v_a_4132_, v___x_4131_);
v___x_4157_ = lean_uint64_dec_eq(v___x_4155_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4159_; 
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4154_);
v___x_4159_ = v___x_4149_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_snd_4147_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
v_a_4141_ = v___x_4159_;
goto v___jp_4140_;
}
}
else
{
uint8_t v___x_4161_; 
v___x_4161_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4152_, v_c_4133_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4163_ = lean_nat_add(v_snd_4147_, v___x_4162_);
lean_dec(v_snd_4147_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 1, v___x_4163_);
lean_ctor_set(v___x_4149_, 0, v___x_4154_);
v___x_4165_ = v___x_4149_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
v_a_4141_ = v___x_4165_;
goto v___jp_4140_;
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
lean_inc(v_snd_4147_);
v___x_4167_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4167_, 0, v_numDigits_4134_);
lean_ctor_set(v___x_4167_, 1, v_snd_4147_);
lean_ctor_set_uint64(v___x_4167_, sizeof(void*)*2, v_a_4132_);
v___x_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4168_);
v___x_4170_ = v___x_4149_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4168_);
lean_ctor_set(v_reuseFailAlloc_4172_, 1, v_snd_4147_);
v___x_4170_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
return v___x_4171_;
}
}
}
}
}
v___jp_4140_:
{
size_t v___x_4142_; size_t v___x_4143_; 
v___x_4142_ = ((size_t)1ULL);
v___x_4143_ = lean_usize_add(v_i_4137_, v___x_4142_);
v_i_4137_ = v___x_4143_;
v_b_4138_ = v_a_4141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4175_, lean_object* v_a_4176_, lean_object* v_c_4177_, lean_object* v_numDigits_4178_, lean_object* v_as_4179_, lean_object* v_sz_4180_, lean_object* v_i_4181_, lean_object* v_b_4182_, lean_object* v___y_4183_){
_start:
{
uint64_t v___x_7695__boxed_4184_; uint64_t v_a_7696__boxed_4185_; size_t v_sz_boxed_4186_; size_t v_i_boxed_4187_; lean_object* v_res_4188_; 
v___x_7695__boxed_4184_ = lean_unbox_uint64(v___x_4175_);
lean_dec_ref(v___x_4175_);
v_a_7696__boxed_4185_ = lean_unbox_uint64(v_a_4176_);
lean_dec_ref(v_a_4176_);
v_sz_boxed_4186_ = lean_unbox_usize(v_sz_4180_);
lean_dec(v_sz_4180_);
v_i_boxed_4187_ = lean_unbox_usize(v_i_4181_);
lean_dec(v_i_4181_);
v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7695__boxed_4184_, v_a_7696__boxed_4185_, v_c_4177_, v_numDigits_4178_, v_as_4179_, v_sz_boxed_4186_, v_i_boxed_4187_, v_b_4182_);
lean_dec_ref(v_as_4179_);
lean_dec_ref(v_c_4177_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4193_, lean_object* v_candidates_x3f_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v___f_4206_; lean_object* v___x_4207_; 
v___f_4206_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4207_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4206_, v_candidates_x3f_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v_candidates_4209_; lean_object* v_numDigits_4210_; lean_object* v___x_4211_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
v_candidates_4209_ = lean_ctor_get(v_a_4208_, 0);
lean_inc_ref(v_candidates_4209_);
v_numDigits_4210_ = lean_ctor_get(v_a_4208_, 1);
lean_inc(v_numDigits_4210_);
lean_dec(v_a_4208_);
v___x_4211_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4193_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; uint64_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; size_t v_sz_4220_; size_t v___x_4221_; uint64_t v___x_4222_; lean_object* v___x_4223_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4211_, 1);
v___x_4213_ = lean_unsigned_to_nat(64u);
v___x_4214_ = lean_unsigned_to_nat(4u);
v___x_4215_ = lean_nat_mul(v___x_4214_, v_numDigits_4210_);
v___x_4216_ = lean_nat_sub(v___x_4213_, v___x_4215_);
lean_dec(v___x_4215_);
v___x_4217_ = lean_uint64_of_nat(v___x_4216_);
lean_dec(v___x_4216_);
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4219_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4220_ = lean_array_size(v_candidates_4209_);
v___x_4221_ = ((size_t)0ULL);
v___x_4222_ = lean_unbox_uint64(v_a_4212_);
lean_inc(v_numDigits_4210_);
v___x_4223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4217_, v___x_4222_, v_c_4193_, v_numDigits_4210_, v_candidates_4209_, v_sz_4220_, v___x_4221_, v___x_4219_);
lean_dec_ref(v_candidates_4209_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4238_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4226_ = v___x_4223_;
v_isShared_4227_ = v_isSharedCheck_4238_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4223_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4238_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v_fst_4228_; 
v_fst_4228_ = lean_ctor_get(v_a_4224_, 0);
lean_inc(v_fst_4228_);
lean_dec(v_a_4224_);
if (lean_obj_tag(v_fst_4228_) == 0)
{
lean_object* v___x_4229_; uint64_t v___x_4230_; lean_object* v___x_4232_; 
v___x_4229_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4229_, 0, v_numDigits_4210_);
lean_ctor_set(v___x_4229_, 1, v___x_4218_);
v___x_4230_ = lean_unbox_uint64(v_a_4212_);
lean_dec(v_a_4212_);
lean_ctor_set_uint64(v___x_4229_, sizeof(void*)*2, v___x_4230_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v___x_4229_);
v___x_4232_ = v___x_4226_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4229_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
else
{
lean_object* v_val_4234_; lean_object* v___x_4236_; 
lean_dec(v_a_4212_);
lean_dec(v_numDigits_4210_);
v_val_4234_ = lean_ctor_get(v_fst_4228_, 0);
lean_inc(v_val_4234_);
lean_dec_ref_known(v_fst_4228_, 1);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v_val_4234_);
v___x_4236_ = v___x_4226_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_val_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v_a_4212_);
lean_dec(v_numDigits_4210_);
v_a_4239_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4223_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4223_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v_numDigits_4210_);
lean_dec_ref(v_candidates_4209_);
v_a_4247_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4211_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4211_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
v_a_4255_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4207_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4207_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4263_, lean_object* v_candidates_x3f_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4263_, v_candidates_x3f_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_c_4263_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4277_, uint64_t v_a_4278_, lean_object* v_c_4279_, lean_object* v_numDigits_4280_, lean_object* v_as_4281_, size_t v_sz_4282_, size_t v_i_4283_, lean_object* v_b_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4277_, v_a_4278_, v_c_4279_, v_numDigits_4280_, v_as_4281_, v_sz_4282_, v_i_4283_, v_b_4284_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4297_ = _args[0];
lean_object* v_a_4298_ = _args[1];
lean_object* v_c_4299_ = _args[2];
lean_object* v_numDigits_4300_ = _args[3];
lean_object* v_as_4301_ = _args[4];
lean_object* v_sz_4302_ = _args[5];
lean_object* v_i_4303_ = _args[6];
lean_object* v_b_4304_ = _args[7];
lean_object* v___y_4305_ = _args[8];
lean_object* v___y_4306_ = _args[9];
lean_object* v___y_4307_ = _args[10];
lean_object* v___y_4308_ = _args[11];
lean_object* v___y_4309_ = _args[12];
lean_object* v___y_4310_ = _args[13];
lean_object* v___y_4311_ = _args[14];
lean_object* v___y_4312_ = _args[15];
lean_object* v___y_4313_ = _args[16];
lean_object* v___y_4314_ = _args[17];
lean_object* v___y_4315_ = _args[18];
_start:
{
uint64_t v___x_7894__boxed_4316_; uint64_t v_a_7895__boxed_4317_; size_t v_sz_boxed_4318_; size_t v_i_boxed_4319_; lean_object* v_res_4320_; 
v___x_7894__boxed_4316_ = lean_unbox_uint64(v___x_4297_);
lean_dec_ref(v___x_4297_);
v_a_7895__boxed_4317_ = lean_unbox_uint64(v_a_4298_);
lean_dec_ref(v_a_4298_);
v_sz_boxed_4318_ = lean_unbox_usize(v_sz_4302_);
lean_dec(v_sz_4302_);
v_i_boxed_4319_ = lean_unbox_usize(v_i_4303_);
lean_dec(v_i_4303_);
v_res_4320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7894__boxed_4316_, v_a_7895__boxed_4317_, v_c_4299_, v_numDigits_4300_, v_as_4301_, v_sz_boxed_4318_, v_i_boxed_4319_, v_b_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v_as_4301_);
lean_dec_ref(v_c_4299_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4345_, lean_object* v_a_4346_){
_start:
{
lean_object* v_numDigits_4348_; uint64_t v_anchor_4349_; lean_object* v_ordinal_4350_; lean_object* v___x_4351_; 
v_numDigits_4348_ = lean_ctor_get(v_info_4345_, 0);
v_anchor_4349_ = lean_ctor_get_uint64(v_info_4345_, sizeof(void*)*2);
v_ordinal_4350_ = lean_ctor_get(v_info_4345_, 1);
v___x_4351_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4348_, v_anchor_4349_, v_a_4346_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4388_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4388_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4388_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_nat_dec_eq(v_ordinal_4350_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v_ref_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
v_ref_4358_ = lean_ctor_get(v_a_4346_, 2);
v___x_4359_ = l_Lean_SourceInfo_fromRef(v_ref_4358_, v___x_4357_);
v___x_4360_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4361_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4359_, 3);
v___x_4362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4359_);
lean_ctor_set(v___x_4362_, 1, v___x_4360_);
v___x_4363_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4364_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4359_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_unsigned_to_nat(1u);
v___x_4367_ = lean_nat_add(v_ordinal_4350_, v___x_4366_);
v___x_4368_ = l_Nat_reprFast(v___x_4367_);
v___x_4369_ = lean_box(2);
v___x_4370_ = l_Lean_Syntax_mkNumLit(v___x_4368_, v___x_4369_);
v___x_4371_ = l_Lean_Syntax_node3(v___x_4359_, v___x_4363_, v_a_4352_, v___x_4365_, v___x_4370_);
v___x_4372_ = l_Lean_Syntax_node2(v___x_4359_, v___x_4361_, v___x_4362_, v___x_4371_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4372_);
v___x_4374_ = v___x_4354_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
else
{
lean_object* v_ref_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4386_; 
v_ref_4376_ = lean_ctor_get(v_a_4346_, 2);
v___x_4377_ = 0;
v___x_4378_ = l_Lean_SourceInfo_fromRef(v_ref_4376_, v___x_4377_);
v___x_4379_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4380_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4378_, 2);
v___x_4381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4378_);
lean_ctor_set(v___x_4381_, 1, v___x_4379_);
v___x_4382_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4383_ = l_Lean_Syntax_node1(v___x_4378_, v___x_4382_, v_a_4352_);
v___x_4384_ = l_Lean_Syntax_node2(v___x_4378_, v___x_4380_, v___x_4381_, v___x_4383_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4384_);
v___x_4386_ = v___x_4354_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
else
{
return v___x_4351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4389_, v_a_4390_);
lean_dec_ref(v_a_4390_);
lean_dec_ref(v_info_4389_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4393_, v_a_4394_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4398_, v_a_4399_, v_a_4400_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_info_4398_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(lean_object* v_proof_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v_p_4434_; lean_object* v___x_4437_; 
lean_inc_ref(v_proof_4415_);
v___x_4437_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4415_, v_a_4417_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4464_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4440_ = v___x_4437_;
v_isShared_4441_ = v_isSharedCheck_4464_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4464_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; uint8_t v___x_4443_; 
v___x_4442_ = l_Lean_Expr_cleanupAnnotations(v_a_4438_);
lean_dec(v_a_4438_);
v___x_4443_ = l_Lean_Expr_isApp(v___x_4442_);
if (v___x_4443_ == 0)
{
lean_dec_ref(v___x_4442_);
lean_del_object(v___x_4440_);
v___y_4422_ = v_a_4416_;
v___y_4423_ = v_a_4417_;
v___y_4424_ = v_a_4418_;
v___y_4425_ = v_a_4419_;
goto v___jp_4421_;
}
else
{
lean_object* v___x_4444_; uint8_t v___x_4445_; 
v___x_4444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4442_);
v___x_4445_ = l_Lean_Expr_isApp(v___x_4444_);
if (v___x_4445_ == 0)
{
lean_dec_ref(v___x_4444_);
lean_dec_ref(v___x_4442_);
lean_del_object(v___x_4440_);
v___y_4422_ = v_a_4416_;
v___y_4423_ = v_a_4417_;
v___y_4424_ = v_a_4418_;
v___y_4425_ = v_a_4419_;
goto v___jp_4421_;
}
else
{
lean_object* v_arg_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v_arg_4446_ = lean_ctor_get(v___x_4442_, 1);
lean_inc_ref(v_arg_4446_);
lean_dec_ref(v___x_4442_);
v___x_4447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4444_);
v___x_4448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4449_ = l_Lean_Expr_isConstOf(v___x_4447_, v___x_4448_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; uint8_t v___x_4451_; 
lean_dec_ref(v___x_4444_);
lean_del_object(v___x_4440_);
v___x_4450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4451_ = l_Lean_Expr_isConstOf(v___x_4447_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; uint8_t v___x_4453_; 
v___x_4452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4453_ = l_Lean_Expr_isConstOf(v___x_4447_, v___x_4452_);
lean_dec_ref(v___x_4447_);
if (v___x_4453_ == 0)
{
lean_dec_ref(v_arg_4446_);
v___y_4422_ = v_a_4416_;
v___y_4423_ = v_a_4417_;
v___y_4424_ = v_a_4418_;
v___y_4425_ = v_a_4419_;
goto v___jp_4421_;
}
else
{
lean_dec_ref(v_proof_4415_);
v_p_4434_ = v_arg_4446_;
goto v___jp_4433_;
}
}
else
{
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_proof_4415_);
v_p_4434_ = v_arg_4446_;
goto v___jp_4433_;
}
}
else
{
lean_object* v_arg_4454_; uint8_t v___x_4455_; 
lean_dec_ref(v___x_4447_);
lean_dec_ref(v_proof_4415_);
v_arg_4454_ = lean_ctor_get(v___x_4444_, 1);
lean_inc_ref(v_arg_4454_);
lean_dec_ref(v___x_4444_);
v___x_4455_ = l_Lean_Expr_isFalse(v_arg_4454_);
lean_dec_ref(v_arg_4454_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_dec_ref(v_arg_4446_);
v___x_4456_ = lean_box(0);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4456_);
v___x_4458_ = v___x_4440_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
else
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v_arg_4446_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4460_);
v___x_4462_ = v___x_4440_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec_ref(v_proof_4415_);
v_a_4465_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4437_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4437_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
v___jp_4421_:
{
if (lean_obj_tag(v_proof_4415_) == 6)
{
lean_object* v_body_4426_; uint8_t v___x_4427_; 
v_body_4426_ = lean_ctor_get(v_proof_4415_, 2);
lean_inc_ref(v_body_4426_);
lean_dec_ref_known(v_proof_4415_, 3);
v___x_4427_ = l_Lean_Expr_hasLooseBVars(v_body_4426_);
if (v___x_4427_ == 0)
{
v_proof_4415_ = v_body_4426_;
v_a_4416_ = v___y_4422_;
v_a_4417_ = v___y_4423_;
v_a_4418_ = v___y_4424_;
v_a_4419_ = v___y_4425_;
goto _start;
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref(v_body_4426_);
v___x_4429_ = lean_box(0);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
lean_dec_ref(v_proof_4415_);
v___x_4431_ = lean_box(0);
v___x_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
}
v___jp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v_p_4434_);
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___boxed(lean_object* v_proof_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_proof_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(lean_object* v_e_4480_, lean_object* v___y_4481_){
_start:
{
uint8_t v___x_4483_; 
v___x_4483_ = l_Lean_Expr_hasMVar(v_e_4480_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v_e_4480_);
return v___x_4484_;
}
else
{
lean_object* v___x_4485_; lean_object* v_mctx_4486_; lean_object* v___x_4487_; lean_object* v_fst_4488_; lean_object* v_snd_4489_; lean_object* v___x_4490_; lean_object* v_cache_4491_; lean_object* v_zetaDeltaFVarIds_4492_; lean_object* v_postponed_4493_; lean_object* v_diag_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4503_; 
v___x_4485_ = lean_st_ref_get(v___y_4481_);
v_mctx_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc_ref(v_mctx_4486_);
lean_dec(v___x_4485_);
v___x_4487_ = l_Lean_instantiateMVarsCore(v_mctx_4486_, v_e_4480_);
v_fst_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_fst_4488_);
v_snd_4489_ = lean_ctor_get(v___x_4487_, 1);
lean_inc(v_snd_4489_);
lean_dec_ref(v___x_4487_);
v___x_4490_ = lean_st_ref_take(v___y_4481_);
v_cache_4491_ = lean_ctor_get(v___x_4490_, 1);
v_zetaDeltaFVarIds_4492_ = lean_ctor_get(v___x_4490_, 2);
v_postponed_4493_ = lean_ctor_get(v___x_4490_, 3);
v_diag_4494_ = lean_ctor_get(v___x_4490_, 4);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v___x_4490_, 0);
lean_dec(v_unused_4504_);
v___x_4496_ = v___x_4490_;
v_isShared_4497_ = v_isSharedCheck_4503_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_diag_4494_);
lean_inc(v_postponed_4493_);
lean_inc(v_zetaDeltaFVarIds_4492_);
lean_inc(v_cache_4491_);
lean_dec(v___x_4490_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4503_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v_snd_4489_);
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_snd_4489_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_cache_4491_);
lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_zetaDeltaFVarIds_4492_);
lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_postponed_4493_);
lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_diag_4494_);
v___x_4499_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = lean_st_ref_put(v___y_4481_, v___x_4499_);
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v_fst_4488_);
return v___x_4501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg___boxed(lean_object* v_e_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4505_, v___y_4506_);
lean_dec(v___y_4506_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(lean_object* v_e_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4509_, v___y_4511_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___boxed(lean_object* v_e_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(v_e_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(lean_object* v_mvarId_4523_, lean_object* v_x_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4523_, v_x_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4530_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
v_a_4539_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4530_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4530_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4547_, lean_object* v_x_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4547_, v_x_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(lean_object* v_00_u03b1_4555_, lean_object* v_mvarId_4556_, lean_object* v_x_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4556_, v_x_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___boxed(lean_object* v_00_u03b1_4564_, lean_object* v_mvarId_4565_, lean_object* v_x_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(v_00_u03b1_4564_, v_mvarId_4565_, v_x_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(lean_object* v___x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4590_; 
v___x_4579_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v___x_4573_, v___y_4575_);
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4582_ = v___x_4579_;
v_isShared_4583_ = v_isSharedCheck_4590_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4579_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4590_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
uint8_t v___x_4584_; 
v___x_4584_ = l_Lean_Expr_hasSyntheticSorry(v_a_4580_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; 
lean_del_object(v___x_4582_);
v___x_4585_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_a_4580_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
return v___x_4585_;
}
else
{
lean_object* v___x_4586_; lean_object* v___x_4588_; 
lean_dec(v_a_4580_);
v___x_4586_ = lean_box(0);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 0, v___x_4586_);
v___x_4588_ = v___x_4582_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed(lean_object* v___x_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(v___x_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(lean_object* v_mvarId_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v___x_4604_; lean_object* v___f_4605_; lean_object* v___x_4606_; 
lean_inc(v_mvarId_4598_);
v___x_4604_ = l_Lean_mkMVar(v_mvarId_4598_);
v___f_4605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4605_, 0, v___x_4604_);
v___x_4606_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4598_, v___f_4605_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___boxed(lean_object* v_mvarId_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(lean_object* v_mvarId_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg___boxed(lean_object* v_mvarId_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(v_mvarId_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(lean_object* v_mvarId_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4628_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___boxed(lean_object* v_mvarId_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(v_mvarId_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_zero_4654_; uint8_t v_isZero_4655_; 
v_zero_4654_ = lean_unsigned_to_nat(0u);
v_isZero_4655_ = lean_nat_dec_eq(v_a_4652_, v_zero_4654_);
if (v_isZero_4655_ == 0)
{
if (lean_obj_tag(v_a_4653_) == 6)
{
lean_object* v_body_4656_; lean_object* v_one_4657_; lean_object* v_n_4658_; 
v_body_4656_ = lean_ctor_get(v_a_4653_, 2);
v_one_4657_ = lean_unsigned_to_nat(1u);
v_n_4658_ = lean_nat_sub(v_a_4652_, v_one_4657_);
lean_dec(v_a_4652_);
v_a_4652_ = v_n_4658_;
v_a_4653_ = v_body_4656_;
goto _start;
}
else
{
lean_dec(v_a_4652_);
lean_inc_ref(v_a_4653_);
return v_a_4653_;
}
}
else
{
lean_dec(v_a_4652_);
lean_inc_ref(v_a_4653_);
return v_a_4653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody___boxed(lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v_a_4660_, v_a_4661_);
lean_dec_ref(v_a_4661_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(lean_object* v_mvarId_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; lean_object* v_mctx_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4666_ = lean_st_ref_get(v___y_4664_);
v_mctx_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc_ref(v_mctx_4667_);
lean_dec(v___x_4666_);
v___x_4668_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_4667_, v_mvarId_4663_);
lean_dec_ref(v_mctx_4667_);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg___boxed(lean_object* v_mvarId_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4670_, v___y_4671_);
lean_dec(v___y_4671_);
lean_dec(v_mvarId_4670_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(lean_object* v_mvarId_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4674_, v___y_4681_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___boxed(lean_object* v_mvarId_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(v_mvarId_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec(v_mvarId_4686_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(lean_object* v_mvarId_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v___x_4701_; lean_object* v_mctx_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4701_ = lean_st_ref_get(v___y_4699_);
v_mctx_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc_ref(v_mctx_4702_);
lean_dec(v___x_4701_);
v___x_4703_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_4702_, v_mvarId_4698_);
lean_dec_ref(v_mctx_4702_);
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg___boxed(lean_object* v_mvarId_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4705_, v___y_4706_);
lean_dec(v___y_4706_);
lean_dec(v_mvarId_4705_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(lean_object* v_mvarId_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4709_, v___y_4716_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___boxed(lean_object* v_mvarId_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(v_mvarId_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec(v_mvarId_4721_);
return v_res_4732_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(lean_object* v___x_4733_, lean_object* v_x_4734_){
_start:
{
if (lean_obj_tag(v_x_4734_) == 0)
{
uint8_t v___x_4735_; 
v___x_4735_ = 1;
return v___x_4735_;
}
else
{
lean_object* v_head_4736_; lean_object* v_tail_4737_; lean_object* v_fst_4738_; lean_object* v_snd_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; uint8_t v___x_4744_; 
v_head_4736_ = lean_ctor_get(v_x_4734_, 0);
v_tail_4737_ = lean_ctor_get(v_x_4734_, 1);
v_fst_4738_ = lean_ctor_get(v_head_4736_, 0);
v_snd_4739_ = lean_ctor_get(v_head_4736_, 1);
v___x_4740_ = lean_unsigned_to_nat(1u);
v___x_4741_ = lean_nat_sub(v___x_4733_, v___x_4740_);
v___x_4742_ = lean_nat_sub(v___x_4741_, v_snd_4739_);
lean_dec(v___x_4741_);
v___x_4743_ = l_Lean_mkBVar(v___x_4742_);
v___x_4744_ = lean_expr_eqv(v_fst_4738_, v___x_4743_);
lean_dec_ref(v___x_4743_);
if (v___x_4744_ == 0)
{
return v___x_4744_;
}
else
{
v_x_4734_ = v_tail_4737_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0___boxed(lean_object* v___x_4746_, lean_object* v_x_4747_){
_start:
{
uint8_t v_res_4748_; lean_object* v_r_4749_; 
v_res_4748_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4746_, v_x_4747_);
lean_dec(v_x_4747_);
lean_dec(v___x_4746_);
v_r_4749_ = lean_box(v_res_4748_);
return v_r_4749_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(lean_object* v_k_4750_, lean_object* v_t_4751_){
_start:
{
if (lean_obj_tag(v_t_4751_) == 0)
{
lean_object* v_k_4752_; lean_object* v_l_4753_; lean_object* v_r_4754_; uint8_t v___x_4755_; 
v_k_4752_ = lean_ctor_get(v_t_4751_, 1);
v_l_4753_ = lean_ctor_get(v_t_4751_, 3);
v_r_4754_ = lean_ctor_get(v_t_4751_, 4);
v___x_4755_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4750_, v_k_4752_);
switch(v___x_4755_)
{
case 0:
{
v_t_4751_ = v_l_4753_;
goto _start;
}
case 1:
{
uint8_t v___x_4757_; 
v___x_4757_ = 1;
return v___x_4757_;
}
default: 
{
v_t_4751_ = v_r_4754_;
goto _start;
}
}
}
else
{
uint8_t v___x_4759_; 
v___x_4759_ = 0;
return v___x_4759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg___boxed(lean_object* v_k_4760_, lean_object* v_t_4761_){
_start:
{
uint8_t v_res_4762_; lean_object* v_r_4763_; 
v_res_4762_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4760_, v_t_4761_);
lean_dec(v_t_4761_);
lean_dec(v_k_4760_);
v_r_4763_ = lean_box(v_res_4762_);
return v_r_4763_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(lean_object* v_a_4764_, lean_object* v_as_4765_, size_t v_i_4766_, size_t v_stop_4767_){
_start:
{
uint8_t v___x_4768_; 
v___x_4768_ = lean_usize_dec_eq(v_i_4766_, v_stop_4767_);
if (v___x_4768_ == 0)
{
lean_object* v_fvars_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
v_fvars_4769_ = lean_ctor_get(v_a_4764_, 0);
v___x_4770_ = lean_array_uget_borrowed(v_as_4765_, v_i_4766_);
v___x_4771_ = l_Lean_Expr_fvarId_x21(v___x_4770_);
v___x_4772_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v___x_4771_, v_fvars_4769_);
lean_dec(v___x_4771_);
if (v___x_4772_ == 0)
{
size_t v___x_4773_; size_t v___x_4774_; 
v___x_4773_ = ((size_t)1ULL);
v___x_4774_ = lean_usize_add(v_i_4766_, v___x_4773_);
v_i_4766_ = v___x_4774_;
goto _start;
}
else
{
return v___x_4772_;
}
}
else
{
uint8_t v___x_4776_; 
v___x_4776_ = 0;
return v___x_4776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3___boxed(lean_object* v_a_4777_, lean_object* v_as_4778_, lean_object* v_i_4779_, lean_object* v_stop_4780_){
_start:
{
size_t v_i_boxed_4781_; size_t v_stop_boxed_4782_; uint8_t v_res_4783_; lean_object* v_r_4784_; 
v_i_boxed_4781_ = lean_unbox_usize(v_i_4779_);
lean_dec(v_i_4779_);
v_stop_boxed_4782_ = lean_unbox_usize(v_stop_4780_);
lean_dec(v_stop_4780_);
v_res_4783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4777_, v_as_4778_, v_i_boxed_4781_, v_stop_boxed_4782_);
lean_dec_ref(v_as_4778_);
lean_dec_ref(v_a_4777_);
v_r_4784_ = lean_box(v_res_4783_);
return v_r_4784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_4785_; lean_object* v_dummy_4786_; 
v___x_4785_ = lean_box(0);
v_dummy_4786_ = l_Lean_Expr_sort___override(v___x_4785_);
return v_dummy_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_mvarId_4787_, lean_object* v_proof_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v_p_4800_; lean_object* v_proof_4803_; lean_object* v___y_4805_; lean_object* v___y_4806_; lean_object* v___y_4807_; lean_object* v___y_4808_; lean_object* v___y_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v___y_4881_; lean_object* v___y_4882_; lean_object* v___y_4883_; lean_object* v___y_4884_; lean_object* v___y_4885_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___x_4926_; 
v_proof_4803_ = l_Lean_Expr_headBeta(v_proof_4788_);
v___x_4926_ = l_Lean_Expr_getAppFn(v_proof_4803_);
if (lean_obj_tag(v___x_4926_) == 2)
{
lean_object* v_mvarId_4927_; lean_object* v___x_4928_; 
v_mvarId_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc(v_mvarId_4927_);
lean_dec_ref_known(v___x_4926_, 1);
v___x_4928_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4927_, v_a_4795_);
lean_dec(v_mvarId_4927_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
if (lean_obj_tag(v_a_4929_) == 1)
{
lean_object* v_val_4930_; lean_object* v_dummy_4931_; lean_object* v_nargs_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v_val_4930_ = lean_ctor_get(v_a_4929_, 0);
lean_inc(v_val_4930_);
lean_dec_ref_known(v_a_4929_, 1);
v_dummy_4931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4932_ = l_Lean_Expr_getAppNumArgs(v_proof_4803_);
lean_inc(v_nargs_4932_);
v___x_4933_ = lean_mk_array(v_nargs_4932_, v_dummy_4931_);
v___x_4934_ = lean_unsigned_to_nat(1u);
v___x_4935_ = lean_nat_sub(v_nargs_4932_, v___x_4934_);
lean_dec(v_nargs_4932_);
v___x_4936_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_proof_4803_, v___x_4933_, v___x_4935_);
v___x_4937_ = l_Lean_Expr_beta(v_val_4930_, v___x_4936_);
v_proof_4788_ = v___x_4937_;
goto _start;
}
else
{
lean_dec(v_a_4929_);
v___y_4881_ = v_a_4789_;
v___y_4882_ = v_a_4790_;
v___y_4883_ = v_a_4791_;
v___y_4884_ = v_a_4792_;
v___y_4885_ = v_a_4793_;
v___y_4886_ = v_a_4794_;
v___y_4887_ = v_a_4795_;
v___y_4888_ = v_a_4796_;
v___y_4889_ = v_a_4797_;
goto v___jp_4880_;
}
}
else
{
lean_dec_ref(v_proof_4803_);
lean_dec(v_mvarId_4787_);
return v___x_4928_;
}
}
else
{
lean_dec_ref(v___x_4926_);
v___y_4881_ = v_a_4789_;
v___y_4882_ = v_a_4790_;
v___y_4883_ = v_a_4791_;
v___y_4884_ = v_a_4792_;
v___y_4885_ = v_a_4793_;
v___y_4886_ = v_a_4794_;
v___y_4887_ = v_a_4795_;
v___y_4888_ = v_a_4796_;
v___y_4889_ = v_a_4797_;
goto v___jp_4880_;
}
v___jp_4799_:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4801_, 0, v_p_4800_);
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
v___jp_4804_:
{
if (lean_obj_tag(v_proof_4803_) == 6)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4814_ = l_Lean_Expr_getNumHeadLambdas(v_proof_4803_);
lean_inc(v___x_4814_);
v___x_4815_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v___x_4814_, v_proof_4803_);
lean_dec_ref_known(v_proof_4803_, 3);
v___x_4816_ = l_Lean_Expr_hasLooseBVars(v___x_4815_);
if (v___x_4816_ == 0)
{
lean_dec(v___x_4814_);
v_proof_4788_ = v___x_4815_;
v_a_4789_ = v___y_4805_;
v_a_4790_ = v___y_4806_;
v_a_4791_ = v___y_4807_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
goto _start;
}
else
{
lean_object* v___x_4818_; 
v___x_4818_ = l_Lean_Expr_getAppFn(v___x_4815_);
if (lean_obj_tag(v___x_4818_) == 2)
{
lean_object* v_mvarId_4819_; lean_object* v_dummy_4820_; lean_object* v_nargs_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v_mvarId_4819_ = lean_ctor_get(v___x_4818_, 0);
lean_inc(v_mvarId_4819_);
lean_dec_ref_known(v___x_4818_, 1);
v_dummy_4820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4821_ = l_Lean_Expr_getAppNumArgs(v___x_4815_);
lean_inc(v_nargs_4821_);
v___x_4822_ = lean_mk_array(v_nargs_4821_, v_dummy_4820_);
v___x_4823_ = lean_unsigned_to_nat(1u);
v___x_4824_ = lean_nat_sub(v_nargs_4821_, v___x_4823_);
lean_dec(v_nargs_4821_);
v___x_4825_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_4815_, v___x_4822_, v___x_4824_);
v___x_4826_ = lean_array_get_size(v___x_4825_);
v___x_4827_ = lean_nat_dec_eq(v___x_4826_, v___x_4814_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; 
lean_dec_ref(v___x_4825_);
lean_dec(v_mvarId_4819_);
lean_dec(v___x_4814_);
v___x_4828_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4787_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4828_;
}
else
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4829_ = lean_array_to_list(v___x_4825_);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = l_List_zipIdxTR___redArg(v___x_4829_, v___x_4830_);
v___x_4832_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4814_, v___x_4831_);
lean_dec(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; 
lean_dec(v_mvarId_4819_);
lean_dec(v___x_4814_);
v___x_4833_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4787_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4833_;
}
else
{
lean_object* v___x_4834_; 
v___x_4834_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4819_, v___y_4811_);
lean_dec(v_mvarId_4819_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v_a_4835_; 
v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
lean_inc(v_a_4835_);
lean_dec_ref_known(v___x_4834_, 1);
if (lean_obj_tag(v_a_4835_) == 1)
{
lean_object* v_val_4836_; lean_object* v_fvars_4837_; lean_object* v_mvarIdPending_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; 
v_val_4836_ = lean_ctor_get(v_a_4835_, 0);
lean_inc(v_val_4836_);
lean_dec_ref_known(v_a_4835_, 1);
v_fvars_4837_ = lean_ctor_get(v_val_4836_, 0);
lean_inc_ref(v_fvars_4837_);
v_mvarIdPending_4838_ = lean_ctor_get(v_val_4836_, 1);
lean_inc(v_mvarIdPending_4838_);
lean_dec(v_val_4836_);
v___x_4839_ = lean_array_get_size(v_fvars_4837_);
v___x_4840_ = lean_nat_dec_eq(v___x_4839_, v___x_4814_);
lean_dec(v___x_4814_);
if (v___x_4840_ == 0)
{
lean_object* v___x_4841_; 
lean_dec(v_mvarIdPending_4838_);
lean_dec_ref(v_fvars_4837_);
v___x_4841_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4787_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4841_;
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = l_Lean_mkMVar(v_mvarIdPending_4838_);
lean_inc_ref(v___x_4842_);
v___x_4843_ = l_Lean_Meta_Grind_getProofInfo(v___x_4842_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4859_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4846_ = v___x_4843_;
v_isShared_4847_ = v_isSharedCheck_4859_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4843_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4859_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
uint8_t v___x_4848_; 
v___x_4848_ = lean_nat_dec_lt(v___x_4830_, v___x_4839_);
if (v___x_4848_ == 0)
{
lean_del_object(v___x_4846_);
lean_dec(v_a_4844_);
lean_dec_ref(v_fvars_4837_);
v_proof_4788_ = v___x_4842_;
v_a_4789_ = v___y_4805_;
v_a_4790_ = v___y_4806_;
v_a_4791_ = v___y_4807_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
goto _start;
}
else
{
if (v___x_4848_ == 0)
{
lean_del_object(v___x_4846_);
lean_dec(v_a_4844_);
lean_dec_ref(v_fvars_4837_);
v_proof_4788_ = v___x_4842_;
v_a_4789_ = v___y_4805_;
v_a_4790_ = v___y_4806_;
v_a_4791_ = v___y_4807_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
goto _start;
}
else
{
size_t v___x_4851_; size_t v___x_4852_; uint8_t v___x_4853_; 
v___x_4851_ = ((size_t)0ULL);
v___x_4852_ = lean_usize_of_nat(v___x_4839_);
v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4844_, v_fvars_4837_, v___x_4851_, v___x_4852_);
lean_dec_ref(v_fvars_4837_);
lean_dec(v_a_4844_);
if (v___x_4853_ == 0)
{
lean_del_object(v___x_4846_);
v_proof_4788_ = v___x_4842_;
v_a_4789_ = v___y_4805_;
v_a_4790_ = v___y_4806_;
v_a_4791_ = v___y_4807_;
v_a_4792_ = v___y_4808_;
v_a_4793_ = v___y_4809_;
v_a_4794_ = v___y_4810_;
v_a_4795_ = v___y_4811_;
v_a_4796_ = v___y_4812_;
v_a_4797_ = v___y_4813_;
goto _start;
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4857_; 
lean_dec_ref(v___x_4842_);
lean_dec(v_mvarId_4787_);
v___x_4855_ = lean_box(0);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 0, v___x_4855_);
v___x_4857_ = v___x_4846_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
lean_dec_ref(v___x_4842_);
lean_dec_ref(v_fvars_4837_);
lean_dec(v_mvarId_4787_);
v_a_4860_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4843_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4843_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
}
else
{
lean_object* v___x_4868_; 
lean_dec(v_a_4835_);
lean_dec(v___x_4814_);
v___x_4868_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4787_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4868_;
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v___x_4814_);
lean_dec(v_mvarId_4787_);
v_a_4869_ = lean_ctor_get(v___x_4834_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4834_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4834_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
}
}
else
{
lean_object* v___x_4877_; 
lean_dec_ref(v___x_4818_);
lean_dec_ref(v___x_4815_);
lean_dec(v___x_4814_);
v___x_4877_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4787_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4877_;
}
}
}
else
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
lean_dec_ref(v_proof_4803_);
lean_dec(v_mvarId_4787_);
v___x_4878_ = lean_box(0);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
return v___x_4879_;
}
}
v___jp_4880_:
{
lean_object* v___x_4890_; 
lean_inc_ref(v_proof_4803_);
v___x_4890_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4803_, v___y_4887_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4917_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4893_ = v___x_4890_;
v_isShared_4894_ = v_isSharedCheck_4917_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4890_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4917_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4895_; uint8_t v___x_4896_; 
v___x_4895_ = l_Lean_Expr_cleanupAnnotations(v_a_4891_);
lean_dec(v_a_4891_);
v___x_4896_ = l_Lean_Expr_isApp(v___x_4895_);
if (v___x_4896_ == 0)
{
lean_dec_ref(v___x_4895_);
lean_del_object(v___x_4893_);
v___y_4805_ = v___y_4881_;
v___y_4806_ = v___y_4882_;
v___y_4807_ = v___y_4883_;
v___y_4808_ = v___y_4884_;
v___y_4809_ = v___y_4885_;
v___y_4810_ = v___y_4886_;
v___y_4811_ = v___y_4887_;
v___y_4812_ = v___y_4888_;
v___y_4813_ = v___y_4889_;
goto v___jp_4804_;
}
else
{
lean_object* v___x_4897_; uint8_t v___x_4898_; 
v___x_4897_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4895_);
v___x_4898_ = l_Lean_Expr_isApp(v___x_4897_);
if (v___x_4898_ == 0)
{
lean_dec_ref(v___x_4897_);
lean_dec_ref(v___x_4895_);
lean_del_object(v___x_4893_);
v___y_4805_ = v___y_4881_;
v___y_4806_ = v___y_4882_;
v___y_4807_ = v___y_4883_;
v___y_4808_ = v___y_4884_;
v___y_4809_ = v___y_4885_;
v___y_4810_ = v___y_4886_;
v___y_4811_ = v___y_4887_;
v___y_4812_ = v___y_4888_;
v___y_4813_ = v___y_4889_;
goto v___jp_4804_;
}
else
{
lean_object* v_arg_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
v_arg_4899_ = lean_ctor_get(v___x_4895_, 1);
lean_inc_ref(v_arg_4899_);
lean_dec_ref(v___x_4895_);
v___x_4900_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4897_);
v___x_4901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4902_ = l_Lean_Expr_isConstOf(v___x_4900_, v___x_4901_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4903_; uint8_t v___x_4904_; 
lean_dec_ref(v___x_4897_);
lean_del_object(v___x_4893_);
v___x_4903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4904_ = l_Lean_Expr_isConstOf(v___x_4900_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; uint8_t v___x_4906_; 
v___x_4905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4906_ = l_Lean_Expr_isConstOf(v___x_4900_, v___x_4905_);
lean_dec_ref(v___x_4900_);
if (v___x_4906_ == 0)
{
lean_dec_ref(v_arg_4899_);
v___y_4805_ = v___y_4881_;
v___y_4806_ = v___y_4882_;
v___y_4807_ = v___y_4883_;
v___y_4808_ = v___y_4884_;
v___y_4809_ = v___y_4885_;
v___y_4810_ = v___y_4886_;
v___y_4811_ = v___y_4887_;
v___y_4812_ = v___y_4888_;
v___y_4813_ = v___y_4889_;
goto v___jp_4804_;
}
else
{
lean_dec_ref(v_proof_4803_);
lean_dec(v_mvarId_4787_);
v_p_4800_ = v_arg_4899_;
goto v___jp_4799_;
}
}
else
{
lean_dec_ref(v___x_4900_);
lean_dec_ref(v_proof_4803_);
lean_dec(v_mvarId_4787_);
v_p_4800_ = v_arg_4899_;
goto v___jp_4799_;
}
}
else
{
lean_object* v_arg_4907_; uint8_t v___x_4908_; 
lean_dec_ref(v___x_4900_);
lean_dec_ref(v_proof_4803_);
lean_dec(v_mvarId_4787_);
v_arg_4907_ = lean_ctor_get(v___x_4897_, 1);
lean_inc_ref(v_arg_4907_);
lean_dec_ref(v___x_4897_);
v___x_4908_ = l_Lean_Expr_isFalse(v_arg_4907_);
lean_dec_ref(v_arg_4907_);
if (v___x_4908_ == 0)
{
lean_object* v___x_4909_; lean_object* v___x_4911_; 
lean_dec_ref(v_arg_4899_);
v___x_4909_ = lean_box(0);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v___x_4909_);
v___x_4911_ = v___x_4893_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4913_, 0, v_arg_4899_);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v___x_4913_);
v___x_4915_ = v___x_4893_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4913_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec_ref(v_proof_4803_);
lean_dec(v_mvarId_4787_);
v_a_4918_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4890_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4890_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_mvarId_4939_, lean_object* v_proof_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_4939_, v_proof_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
lean_dec(v_a_4949_);
lean_dec_ref(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
return v_res_4951_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(lean_object* v_00_u03b2_4952_, lean_object* v_k_4953_, lean_object* v_t_4954_){
_start:
{
uint8_t v___x_4955_; 
v___x_4955_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4953_, v_t_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_4956_, lean_object* v_k_4957_, lean_object* v_t_4958_){
_start:
{
uint8_t v_res_4959_; lean_object* v_r_4960_; 
v_res_4959_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(v_00_u03b2_4956_, v_k_4957_, v_t_4958_);
lean_dec(v_t_4958_);
lean_dec(v_k_4957_);
v_r_4960_ = lean_box(v_res_4959_);
return v_r_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(lean_object* v_x_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
lean_object* v___x_4972_; 
lean_inc(v___y_4966_);
lean_inc_ref(v___y_4965_);
lean_inc(v___y_4964_);
lean_inc_ref(v___y_4963_);
lean_inc(v___y_4962_);
v___x_4972_ = lean_apply_10(v_x_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, lean_box(0));
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(v_x_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_mvarId_4985_, lean_object* v_x_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
lean_object* v___f_4997_; lean_object* v___x_4998_; 
lean_inc(v___y_4991_);
lean_inc_ref(v___y_4990_);
lean_inc(v___y_4989_);
lean_inc_ref(v___y_4988_);
lean_inc(v___y_4987_);
v___f_4997_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4997_, 0, v_x_4986_);
lean_closure_set(v___f_4997_, 1, v___y_4987_);
lean_closure_set(v___f_4997_, 2, v___y_4988_);
lean_closure_set(v___f_4997_, 3, v___y_4989_);
lean_closure_set(v___f_4997_, 4, v___y_4990_);
lean_closure_set(v___f_4997_, 5, v___y_4991_);
v___x_4998_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4985_, v___f_4997_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
if (lean_obj_tag(v___x_4998_) == 0)
{
return v___x_4998_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4998_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4998_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_5007_, lean_object* v_x_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5007_, v_x_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_00_u03b1_5020_, lean_object* v_mvarId_5021_, lean_object* v_x_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v___x_5033_; 
v___x_5033_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5021_, v_x_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_00_u03b1_5034_, lean_object* v_mvarId_5035_, lean_object* v_x_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_00_u03b1_5034_, v_mvarId_5035_, v_x_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
lean_dec(v___y_5037_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_5048_, lean_object* v_mvarId_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v___x_5060_; 
lean_inc_ref(v___x_5048_);
v___x_5060_ = l_Lean_Meta_Grind_getProofInfo(v___x_5048_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5073_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5073_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5073_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
uint8_t v_hasSorry_5070_; 
v_hasSorry_5070_ = lean_ctor_get_uint8(v_a_5061_, sizeof(void*)*1);
if (v_hasSorry_5070_ == 0)
{
uint8_t v_hasUnassigned_5071_; 
v_hasUnassigned_5071_ = lean_ctor_get_uint8(v_a_5061_, sizeof(void*)*1 + 1);
lean_dec(v_a_5061_);
if (v_hasUnassigned_5071_ == 0)
{
lean_object* v___x_5072_; 
lean_del_object(v___x_5063_);
v___x_5072_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_5049_, v___x_5048_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
return v___x_5072_;
}
else
{
lean_dec(v_mvarId_5049_);
lean_dec_ref(v___x_5048_);
goto v___jp_5065_;
}
}
else
{
lean_dec(v_a_5061_);
lean_dec(v_mvarId_5049_);
lean_dec_ref(v___x_5048_);
goto v___jp_5065_;
}
v___jp_5065_:
{
lean_object* v___x_5066_; lean_object* v___x_5068_; 
v___x_5066_ = lean_box(0);
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 0, v___x_5066_);
v___x_5068_ = v___x_5063_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5066_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5081_; 
lean_dec(v_mvarId_5049_);
lean_dec_ref(v___x_5048_);
v_a_5074_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_5060_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5060_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_5082_, lean_object* v_mvarId_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_5082_, v_mvarId_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec(v___y_5084_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v___x_5106_; lean_object* v___f_5107_; lean_object* v___x_5108_; 
lean_inc_n(v_mvarId_5095_, 2);
v___x_5106_ = l_Lean_mkMVar(v_mvarId_5095_);
v___f_5107_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5107_, 0, v___x_5106_);
lean_closure_set(v___f_5107_, 1, v_mvarId_5095_);
v___x_5108_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5095_, v___f_5107_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
lean_dec(v_a_5114_);
lean_dec_ref(v_a_5113_);
lean_dec(v_a_5112_);
lean_dec_ref(v_a_5111_);
lean_dec(v_a_5110_);
return v_res_5120_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_5142_){
_start:
{
if (lean_obj_tag(v_x_5142_) == 0)
{
uint8_t v___x_5143_; 
v___x_5143_ = 1;
return v___x_5143_;
}
else
{
lean_object* v_head_5144_; lean_object* v_tail_5145_; lean_object* v___x_5146_; uint8_t v___x_5147_; 
v_head_5144_ = lean_ctor_get(v_x_5142_, 0);
lean_inc_n(v_head_5144_, 2);
v_tail_5145_ = lean_ctor_get(v_x_5142_, 1);
lean_inc(v_tail_5145_);
lean_dec_ref_known(v_x_5142_, 2);
v___x_5146_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_5147_ = l_Lean_Syntax_isOfKind(v_head_5144_, v___x_5146_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; uint8_t v___x_5149_; 
v___x_5148_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_5144_);
v___x_5149_ = l_Lean_Syntax_isOfKind(v_head_5144_, v___x_5148_);
if (v___x_5149_ == 0)
{
lean_dec(v_head_5144_);
v_x_5142_ = v_tail_5145_;
goto _start;
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; uint8_t v___x_5154_; 
v___x_5151_ = lean_unsigned_to_nat(1u);
v___x_5152_ = l_Lean_Syntax_getArg(v_head_5144_, v___x_5151_);
lean_dec(v_head_5144_);
v___x_5153_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5154_ = l_Lean_Syntax_isOfKind(v___x_5152_, v___x_5153_);
if (v___x_5154_ == 0)
{
v_x_5142_ = v_tail_5145_;
goto _start;
}
else
{
lean_dec(v_tail_5145_);
return v___x_5147_;
}
}
}
else
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___x_5156_ = lean_unsigned_to_nat(3u);
v___x_5157_ = l_Lean_Syntax_getArg(v_head_5144_, v___x_5156_);
lean_dec(v_head_5144_);
v___x_5158_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5159_ = l_Lean_Syntax_isOfKind(v___x_5157_, v___x_5158_);
if (v___x_5159_ == 0)
{
v_x_5142_ = v_tail_5145_;
goto _start;
}
else
{
uint8_t v___x_5161_; 
lean_dec(v_tail_5145_);
v___x_5161_ = 0;
return v___x_5161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_5162_){
_start:
{
uint8_t v_res_5163_; lean_object* v_r_5164_; 
v_res_5163_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_5162_);
v_r_5164_ = lean_box(v_res_5163_);
return v_r_5164_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_5165_){
_start:
{
uint8_t v___x_5166_; 
v___x_5166_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_5165_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_5167_){
_start:
{
uint8_t v_res_5168_; lean_object* v_r_5169_; 
v_res_5168_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_5167_);
v_r_5169_ = lean_box(v_res_5168_);
return v_r_5169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_5185_, lean_object* v_a_5186_){
_start:
{
if (lean_obj_tag(v_seq_5185_) == 0)
{
lean_object* v_ref_5188_; uint8_t v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v_ref_5188_ = lean_ctor_get(v_a_5186_, 2);
v___x_5189_ = 0;
v___x_5190_ = l_Lean_SourceInfo_fromRef(v_ref_5188_, v___x_5189_);
v___x_5191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_5192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_5190_);
v___x_5193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5190_);
lean_ctor_set(v___x_5193_, 1, v___x_5191_);
v___x_5194_ = l_Lean_Syntax_node1(v___x_5190_, v___x_5192_, v___x_5193_);
v___x_5195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5195_, 0, v___x_5194_);
return v___x_5195_;
}
else
{
lean_object* v_tail_5196_; 
v_tail_5196_ = lean_ctor_get(v_seq_5185_, 1);
if (lean_obj_tag(v_tail_5196_) == 0)
{
lean_object* v_head_5197_; lean_object* v___x_5198_; 
v_head_5197_ = lean_ctor_get(v_seq_5185_, 0);
lean_inc(v_head_5197_);
lean_dec_ref_known(v_seq_5185_, 2);
v___x_5198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5198_, 0, v_head_5197_);
return v___x_5198_;
}
else
{
lean_object* v_head_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5221_; 
lean_inc(v_tail_5196_);
v_head_5199_ = lean_ctor_get(v_seq_5185_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v_seq_5185_);
if (v_isSharedCheck_5221_ == 0)
{
lean_object* v_unused_5222_; 
v_unused_5222_ = lean_ctor_get(v_seq_5185_, 1);
lean_dec(v_unused_5222_);
v___x_5201_ = v_seq_5185_;
v_isShared_5202_ = v_isSharedCheck_5221_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_head_5199_);
lean_dec(v_seq_5185_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5221_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5203_; lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5220_; 
v___x_5203_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_5196_, v_a_5186_);
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5206_ = v___x_5203_;
v_isShared_5207_ = v_isSharedCheck_5220_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5203_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5220_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v_ref_5208_; uint8_t v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5214_; 
v_ref_5208_ = lean_ctor_get(v_a_5186_, 2);
v___x_5209_ = 0;
v___x_5210_ = l_Lean_SourceInfo_fromRef(v_ref_5208_, v___x_5209_);
v___x_5211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5210_);
if (v_isShared_5202_ == 0)
{
lean_ctor_set_tag(v___x_5201_, 2);
lean_ctor_set(v___x_5201_, 1, v___x_5212_);
lean_ctor_set(v___x_5201_, 0, v___x_5210_);
v___x_5214_ = v___x_5201_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5210_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v___x_5212_);
v___x_5214_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
lean_object* v___x_5215_; lean_object* v___x_5217_; 
v___x_5215_ = l_Lean_Syntax_node3(v___x_5210_, v___x_5211_, v_head_5199_, v___x_5214_, v_a_5204_);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v___x_5215_);
v___x_5217_ = v___x_5206_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5215_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5223_, v_a_5224_);
lean_dec_ref(v_a_5224_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5227_, v_a_5228_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_5232_, v_a_5233_, v_a_5234_);
lean_dec(v_a_5234_);
lean_dec_ref(v_a_5233_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_5237_, lean_object* v_seq_5238_, lean_object* v_a_5239_){
_start:
{
if (lean_obj_tag(v_seq_5238_) == 0)
{
lean_object* v___x_5241_; 
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v_cases_5237_);
return v___x_5241_;
}
else
{
lean_object* v___x_5242_; lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5257_; 
v___x_5242_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5238_, v_a_5239_);
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5257_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5257_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v_ref_5247_; uint8_t v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5255_; 
v_ref_5247_ = lean_ctor_get(v_a_5239_, 2);
v___x_5248_ = 0;
v___x_5249_ = l_Lean_SourceInfo_fromRef(v_ref_5247_, v___x_5248_);
v___x_5250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5249_);
v___x_5252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5249_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = l_Lean_Syntax_node3(v___x_5249_, v___x_5250_, v_cases_5237_, v___x_5252_, v_a_5243_);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v___x_5253_);
v___x_5255_ = v___x_5245_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5253_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_5258_, lean_object* v_seq_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5258_, v_seq_5259_, v_a_5260_);
lean_dec_ref(v_a_5260_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_5263_, lean_object* v_seq_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5263_, v_seq_5264_, v_a_5265_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_5269_, lean_object* v_seq_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_5269_, v_seq_5270_, v_a_5271_, v_a_5272_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
return v_res_5274_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_5275_, lean_object* v_x_5276_){
_start:
{
if (lean_obj_tag(v_x_5275_) == 0)
{
if (lean_obj_tag(v_x_5276_) == 0)
{
uint8_t v___x_5277_; 
v___x_5277_ = 1;
return v___x_5277_;
}
else
{
uint8_t v___x_5278_; 
v___x_5278_ = 0;
return v___x_5278_;
}
}
else
{
if (lean_obj_tag(v_x_5276_) == 0)
{
uint8_t v___x_5279_; 
v___x_5279_ = 0;
return v___x_5279_;
}
else
{
lean_object* v_head_5280_; lean_object* v_tail_5281_; lean_object* v_head_5282_; lean_object* v_tail_5283_; uint8_t v___x_5284_; 
v_head_5280_ = lean_ctor_get(v_x_5275_, 0);
v_tail_5281_ = lean_ctor_get(v_x_5275_, 1);
v_head_5282_ = lean_ctor_get(v_x_5276_, 0);
v_tail_5283_ = lean_ctor_get(v_x_5276_, 1);
v___x_5284_ = l_Lean_Syntax_structEq(v_head_5280_, v_head_5282_);
if (v___x_5284_ == 0)
{
return v___x_5284_;
}
else
{
v_x_5275_ = v_tail_5281_;
v_x_5276_ = v_tail_5283_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_5286_, lean_object* v_x_5287_){
_start:
{
uint8_t v_res_5288_; lean_object* v_r_5289_; 
v_res_5288_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_5286_, v_x_5287_);
lean_dec(v_x_5287_);
lean_dec(v_x_5286_);
v_r_5289_ = lean_box(v_res_5288_);
return v_r_5289_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_5290_, lean_object* v___x_5291_, lean_object* v_as_5292_, size_t v_i_5293_, size_t v_stop_5294_){
_start:
{
uint8_t v___x_5299_; 
v___x_5299_ = lean_usize_dec_eq(v_i_5293_, v_stop_5294_);
if (v___x_5299_ == 0)
{
lean_object* v___x_5300_; uint8_t v___x_5301_; 
v___x_5300_ = lean_array_uget_borrowed(v_as_5292_, v_i_5293_);
v___x_5301_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_5300_, v_alt_5290_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; uint8_t v___x_5303_; 
v___x_5302_ = lean_unsigned_to_nat(0u);
v___x_5303_ = lean_nat_dec_lt(v___x_5302_, v___x_5291_);
if (v___x_5303_ == 0)
{
goto v___jp_5295_;
}
else
{
return v___x_5303_;
}
}
else
{
goto v___jp_5295_;
}
}
else
{
uint8_t v___x_5304_; 
v___x_5304_ = 0;
return v___x_5304_;
}
v___jp_5295_:
{
size_t v___x_5296_; size_t v___x_5297_; 
v___x_5296_ = ((size_t)1ULL);
v___x_5297_ = lean_usize_add(v_i_5293_, v___x_5296_);
v_i_5293_ = v___x_5297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_5305_, lean_object* v___x_5306_, lean_object* v_as_5307_, lean_object* v_i_5308_, lean_object* v_stop_5309_){
_start:
{
size_t v_i_boxed_5310_; size_t v_stop_boxed_5311_; uint8_t v_res_5312_; lean_object* v_r_5313_; 
v_i_boxed_5310_ = lean_unbox_usize(v_i_5308_);
lean_dec(v_i_5308_);
v_stop_boxed_5311_ = lean_unbox_usize(v_stop_5309_);
lean_dec(v_stop_5309_);
v_res_5312_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5305_, v___x_5306_, v_as_5307_, v_i_boxed_5310_, v_stop_boxed_5311_);
lean_dec_ref(v_as_5307_);
lean_dec(v___x_5306_);
lean_dec(v_alt_5305_);
v_r_5313_ = lean_box(v_res_5312_);
return v_r_5313_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_5314_){
_start:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; uint8_t v___x_5317_; 
v___x_5315_ = lean_unsigned_to_nat(0u);
v___x_5316_ = lean_array_get_size(v_alts_5314_);
v___x_5317_ = lean_nat_dec_lt(v___x_5315_, v___x_5316_);
if (v___x_5317_ == 0)
{
uint8_t v___x_5318_; 
v___x_5318_ = 1;
return v___x_5318_;
}
else
{
lean_object* v_alt_5319_; uint8_t v___x_5320_; 
v_alt_5319_ = lean_array_fget_borrowed(v_alts_5314_, v___x_5315_);
lean_inc(v_alt_5319_);
v___x_5320_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_5319_);
if (v___x_5320_ == 0)
{
return v___x_5320_;
}
else
{
if (v___x_5317_ == 0)
{
return v___x_5317_;
}
else
{
size_t v___x_5321_; size_t v___x_5322_; uint8_t v___x_5323_; 
v___x_5321_ = ((size_t)0ULL);
v___x_5322_ = lean_usize_of_nat(v___x_5316_);
v___x_5323_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5319_, v___x_5316_, v_alts_5314_, v___x_5321_, v___x_5322_);
if (v___x_5323_ == 0)
{
return v___x_5317_;
}
else
{
uint8_t v___x_5324_; 
v___x_5324_ = 0;
return v___x_5324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_5325_){
_start:
{
uint8_t v_res_5326_; lean_object* v_r_5327_; 
v_res_5326_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5325_);
lean_dec_ref(v_alts_5325_);
v_r_5327_ = lean_box(v_res_5326_);
return v_r_5327_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_5335_){
_start:
{
if (lean_obj_tag(v_alt_5335_) == 1)
{
lean_object* v_tail_5336_; 
v_tail_5336_ = lean_ctor_get(v_alt_5335_, 1);
if (lean_obj_tag(v_tail_5336_) == 0)
{
lean_object* v_head_5337_; lean_object* v___x_5338_; uint8_t v___x_5339_; 
v_head_5337_ = lean_ctor_get(v_alt_5335_, 0);
lean_inc(v_head_5337_);
lean_dec_ref_known(v_alt_5335_, 2);
v___x_5338_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_5339_ = l_Lean_Syntax_isOfKind(v_head_5337_, v___x_5338_);
return v___x_5339_;
}
else
{
uint8_t v___x_5340_; 
lean_dec_ref_known(v_alt_5335_, 2);
v___x_5340_ = 0;
return v___x_5340_;
}
}
else
{
uint8_t v___x_5341_; 
lean_dec(v_alt_5335_);
v___x_5341_ = 0;
return v___x_5341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_5342_){
_start:
{
uint8_t v_res_5343_; lean_object* v_r_5344_; 
v_res_5343_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_5342_);
v_r_5344_ = lean_box(v_res_5343_);
return v_r_5344_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_5345_, lean_object* v_x_5346_, lean_object* v___y_5347_){
_start:
{
if (lean_obj_tag(v_x_5345_) == 0)
{
lean_object* v___x_5349_; lean_object* v___x_5350_; 
v___x_5349_ = l_List_reverse___redArg(v_x_5346_);
v___x_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5350_, 0, v___x_5349_);
return v___x_5350_;
}
else
{
lean_object* v_head_5351_; lean_object* v_tail_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5370_; 
v_head_5351_ = lean_ctor_get(v_x_5345_, 0);
v_tail_5352_ = lean_ctor_get(v_x_5345_, 1);
v_isSharedCheck_5370_ = !lean_is_exclusive(v_x_5345_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5354_ = v_x_5345_;
v_isShared_5355_ = v_isSharedCheck_5370_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_tail_5352_);
lean_inc(v_head_5351_);
lean_dec(v_x_5345_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5370_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5356_; 
v___x_5356_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_5351_, v___y_5347_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5359_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 1, v_x_5346_);
lean_ctor_set(v___x_5354_, 0, v_a_5357_);
v___x_5359_ = v___x_5354_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5357_);
lean_ctor_set(v_reuseFailAlloc_5361_, 1, v_x_5346_);
v___x_5359_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
v_x_5345_ = v_tail_5352_;
v_x_5346_ = v___x_5359_;
goto _start;
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_del_object(v___x_5354_);
lean_dec(v_tail_5352_);
lean_dec(v_x_5346_);
v_a_5362_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5356_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5356_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_5371_, lean_object* v_x_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5371_, v_x_5372_, v___y_5373_);
lean_dec_ref(v___y_5373_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_5376_, lean_object* v_alts_5377_, uint8_t v_compress_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_seq_5383_; 
if (v_compress_5378_ == 0)
{
goto v___jp_5386_;
}
else
{
uint8_t v___x_5396_; 
v___x_5396_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5377_);
if (v___x_5396_ == 0)
{
goto v___jp_5386_;
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5398_; uint8_t v___x_5399_; 
v___x_5397_ = lean_unsigned_to_nat(0u);
v___x_5398_ = lean_array_get_size(v_alts_5377_);
v___x_5399_ = lean_nat_dec_lt(v___x_5397_, v___x_5398_);
if (v___x_5399_ == 0)
{
lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_dec_ref(v_alts_5377_);
v___x_5400_ = lean_box(0);
v___x_5401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5401_, 0, v_cases_5376_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
return v___x_5402_;
}
else
{
lean_object* v___x_5403_; lean_object* v_firstAlt_5404_; uint8_t v___x_5405_; 
v___x_5403_ = lean_box(0);
v_firstAlt_5404_ = lean_array_get(v___x_5403_, v_alts_5377_, v___x_5397_);
lean_dec_ref(v_alts_5377_);
lean_inc(v_firstAlt_5404_);
v___x_5405_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_5404_);
if (v___x_5405_ == 0)
{
lean_object* v___x_5406_; lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5415_; 
v___x_5406_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5376_, v_firstAlt_5404_, v_a_5379_);
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5409_ = v___x_5406_;
v_isShared_5410_ = v_isSharedCheck_5415_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5406_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5415_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5411_; lean_object* v___x_5413_; 
v___x_5411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5411_, 0, v_a_5407_);
lean_ctor_set(v___x_5411_, 1, v___x_5403_);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v___x_5411_);
v___x_5413_ = v___x_5409_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
else
{
lean_object* v___x_5416_; 
lean_dec(v_cases_5376_);
v___x_5416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5416_, 0, v_firstAlt_5404_);
return v___x_5416_;
}
}
}
}
v___jp_5382_:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5384_, 0, v_cases_5376_);
lean_ctor_set(v___x_5384_, 1, v_seq_5383_);
v___x_5385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5384_);
return v___x_5385_;
}
v___jp_5386_:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; uint8_t v___x_5389_; 
v___x_5387_ = lean_array_get_size(v_alts_5377_);
v___x_5388_ = lean_unsigned_to_nat(1u);
v___x_5389_ = lean_nat_dec_eq(v___x_5387_, v___x_5388_);
if (v___x_5389_ == 0)
{
lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5390_ = lean_array_to_list(v_alts_5377_);
v___x_5391_ = lean_box(0);
v___x_5392_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_5390_, v___x_5391_, v_a_5379_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
lean_inc(v_a_5393_);
lean_dec_ref_known(v___x_5392_, 1);
v_seq_5383_ = v_a_5393_;
goto v___jp_5382_;
}
else
{
lean_dec(v_cases_5376_);
return v___x_5392_;
}
}
else
{
lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5394_ = lean_unsigned_to_nat(0u);
v___x_5395_ = lean_array_fget(v_alts_5377_, v___x_5394_);
lean_dec_ref(v_alts_5377_);
v_seq_5383_ = v___x_5395_;
goto v___jp_5382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_5417_, lean_object* v_alts_5418_, lean_object* v_compress_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_){
_start:
{
uint8_t v_compress_boxed_5423_; lean_object* v_res_5424_; 
v_compress_boxed_5423_ = lean_unbox(v_compress_5419_);
v_res_5424_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_5417_, v_alts_5418_, v_compress_boxed_5423_, v_a_5420_, v_a_5421_);
lean_dec(v_a_5421_);
lean_dec_ref(v_a_5420_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_5425_, lean_object* v_x_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_){
_start:
{
lean_object* v___x_5430_; 
v___x_5430_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5425_, v_x_5426_, v___y_5427_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_5431_, lean_object* v_x_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_5431_, v_x_5432_, v___y_5433_, v___y_5434_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v___x_5440_; lean_object* v_env_5441_; uint8_t v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5440_ = lean_st_ref_get(v___y_5438_);
v_env_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc_ref(v_env_5441_);
lean_dec(v___x_5440_);
v___x_5442_ = l_Lean_Meta_isMatcherAppCore(v_env_5441_, v_e_5437_);
v___x_5443_ = lean_box(v___x_5442_);
v___x_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5445_, v___y_5446_);
lean_dec(v___y_5446_);
lean_dec_ref(v_e_5445_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5449_, v___y_5459_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_){
_start:
{
lean_object* v_res_5474_; 
v_res_5474_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
lean_dec(v___y_5470_);
lean_dec_ref(v___y_5469_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v_e_5462_);
return v_res_5474_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___x_5476_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5477_ = l_Lean_stringToMessageData(v___x_5476_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5478_, lean_object* v_c_5479_, lean_object* v_a_5480_, lean_object* v_numCases_5481_, uint8_t v_isRec_5482_, lean_object* v_anchorInfo_x3f_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v_mvarIds_5496_; lean_object* v___x_5546_; 
v___x_5546_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5478_, v___y_5484_);
if (lean_obj_tag(v___x_5546_) == 0)
{
lean_object* v_a_5547_; lean_object* v___y_5549_; lean_object* v___x_5601_; uint8_t v___x_5604_; 
v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
lean_inc(v_a_5547_);
lean_dec_ref_known(v___x_5546_, 1);
v___x_5601_ = lean_unsigned_to_nat(1u);
v___x_5604_ = lean_nat_dec_lt(v___x_5601_, v_numCases_5481_);
if (v___x_5604_ == 0)
{
if (v_isRec_5482_ == 0)
{
lean_inc(v_a_5547_);
v___y_5549_ = v_a_5547_;
goto v___jp_5548_;
}
else
{
goto v___jp_5602_;
}
}
else
{
goto v___jp_5602_;
}
v___jp_5548_:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5479_);
lean_inc_ref(v___x_5478_);
v___x_5551_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5478_, v___y_5549_, v_numCases_5481_, v___x_5550_, v___y_5487_, v___y_5490_, v___y_5492_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v___x_5552_; 
lean_dec_ref_known(v___x_5551_, 1);
lean_inc_ref(v___x_5478_);
v___x_5552_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5478_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5552_) == 0)
{
lean_object* v_toCold_5553_; lean_object* v_options_5554_; uint8_t v_hasTrace_5555_; 
lean_dec_ref_known(v___x_5552_, 1);
v_toCold_5553_ = lean_ctor_get(v___y_5492_, 0);
v_options_5554_ = lean_ctor_get(v_toCold_5553_, 2);
v_hasTrace_5555_ = lean_ctor_get_uint8(v_options_5554_, sizeof(void*)*1);
if (v_hasTrace_5555_ == 0)
{
lean_dec(v_a_5547_);
goto v___jp_5499_;
}
else
{
lean_object* v_inheritedTraceOptions_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; uint8_t v___x_5559_; 
v_inheritedTraceOptions_5556_ = lean_ctor_get(v_toCold_5553_, 11);
v___x_5557_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5558_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5556_, v_options_5554_, v___x_5558_);
if (v___x_5559_ == 0)
{
lean_dec(v_a_5547_);
goto v___jp_5499_;
}
else
{
lean_object* v___x_5560_; 
v___x_5560_ = l_Lean_Meta_Grind_updateLastTag(v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; 
lean_dec_ref_known(v___x_5560_, 1);
lean_inc_ref(v___x_5478_);
v___x_5561_ = l_Lean_MessageData_ofExpr(v___x_5478_);
v___x_5562_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5561_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
v___x_5564_ = l_Nat_reprFast(v_a_5547_);
v___x_5565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
v___x_5566_ = l_Lean_MessageData_ofFormat(v___x_5565_);
v___x_5567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5563_);
lean_ctor_set(v___x_5567_, 1, v___x_5566_);
v___x_5568_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5557_, v___x_5567_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5568_) == 0)
{
lean_dec_ref_known(v___x_5568_, 1);
goto v___jp_5499_;
}
else
{
lean_object* v_a_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5576_; 
lean_dec(v_anchorInfo_x3f_5483_);
lean_dec(v_a_5480_);
lean_dec_ref(v_c_5479_);
lean_dec_ref(v___x_5478_);
v_a_5569_ = lean_ctor_get(v___x_5568_, 0);
v_isSharedCheck_5576_ = !lean_is_exclusive(v___x_5568_);
if (v_isSharedCheck_5576_ == 0)
{
v___x_5571_ = v___x_5568_;
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_a_5569_);
lean_dec(v___x_5568_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5574_; 
if (v_isShared_5572_ == 0)
{
v___x_5574_ = v___x_5571_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5569_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_dec(v_a_5547_);
lean_dec(v_anchorInfo_x3f_5483_);
lean_dec(v_a_5480_);
lean_dec_ref(v_c_5479_);
lean_dec_ref(v___x_5478_);
v_a_5577_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5560_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5560_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
}
}
else
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec(v_a_5547_);
lean_dec(v_anchorInfo_x3f_5483_);
lean_dec(v_a_5480_);
lean_dec_ref(v_c_5479_);
lean_dec_ref(v___x_5478_);
v_a_5585_ = lean_ctor_get(v___x_5552_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5552_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5552_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
lean_dec(v_a_5547_);
lean_dec(v_anchorInfo_x3f_5483_);
lean_dec(v_a_5480_);
lean_dec_ref(v_c_5479_);
lean_dec_ref(v___x_5478_);
v_a_5593_ = lean_ctor_get(v___x_5551_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5551_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5551_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5551_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
return v___x_5598_;
}
}
}
}
v___jp_5602_:
{
lean_object* v___x_5603_; 
v___x_5603_ = lean_nat_add(v_a_5547_, v___x_5601_);
v___y_5549_ = v___x_5603_;
goto v___jp_5548_;
}
}
else
{
lean_object* v_a_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5612_; 
lean_dec(v_anchorInfo_x3f_5483_);
lean_dec(v_numCases_5481_);
lean_dec(v_a_5480_);
lean_dec_ref(v_c_5479_);
lean_dec_ref(v___x_5478_);
v_a_5605_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5607_ = v___x_5546_;
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_a_5605_);
lean_dec(v___x_5546_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v___x_5610_; 
if (v_isShared_5608_ == 0)
{
v___x_5610_ = v___x_5607_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_a_5605_);
v___x_5610_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
return v___x_5610_;
}
}
}
v___jp_5495_:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5497_, 0, v_mvarIds_5496_);
lean_ctor_set(v___x_5497_, 1, v_anchorInfo_x3f_5483_);
v___x_5498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5497_);
return v___x_5498_;
}
v___jp_5499_:
{
lean_object* v___x_5500_; 
v___x_5500_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5478_, v___y_5493_);
if (lean_obj_tag(v_c_5479_) == 1)
{
lean_object* v_e_5501_; lean_object* v_binderType_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; 
lean_dec_ref(v___x_5500_);
lean_dec_ref(v___x_5478_);
v_e_5501_ = lean_ctor_get(v_c_5479_, 0);
lean_inc_ref(v_e_5501_);
lean_dec_ref_known(v_c_5479_, 2);
v_binderType_5502_ = lean_ctor_get(v_e_5501_, 1);
lean_inc_ref(v_binderType_5502_);
lean_dec_ref(v_e_5501_);
v___x_5503_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5502_);
v___x_5504_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5480_, v___x_5503_, v___y_5486_, v___y_5487_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_a_5505_);
lean_dec_ref_known(v___x_5504_, 1);
v_mvarIds_5496_ = v_a_5505_;
goto v___jp_5495_;
}
else
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5513_; 
lean_dec(v_anchorInfo_x3f_5483_);
v_a_5506_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5508_ = v___x_5504_;
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5504_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v___x_5511_; 
if (v_isShared_5509_ == 0)
{
v___x_5511_ = v___x_5508_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
else
{
lean_object* v_a_5514_; uint8_t v___x_5515_; 
lean_dec_ref(v_c_5479_);
v_a_5514_ = lean_ctor_get(v___x_5500_, 0);
lean_inc(v_a_5514_);
lean_dec_ref(v___x_5500_);
v___x_5515_ = lean_unbox(v_a_5514_);
lean_dec(v_a_5514_);
if (v___x_5515_ == 0)
{
lean_object* v___x_5516_; 
v___x_5516_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5478_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v___x_5518_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref_known(v___x_5516_, 1);
v___x_5518_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5480_, v_a_5517_, v___y_5486_, v___y_5487_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5518_) == 0)
{
lean_object* v_a_5519_; 
v_a_5519_ = lean_ctor_get(v___x_5518_, 0);
lean_inc(v_a_5519_);
lean_dec_ref_known(v___x_5518_, 1);
v_mvarIds_5496_ = v_a_5519_;
goto v___jp_5495_;
}
else
{
lean_object* v_a_5520_; lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5527_; 
lean_dec(v_anchorInfo_x3f_5483_);
v_a_5520_ = lean_ctor_get(v___x_5518_, 0);
v_isSharedCheck_5527_ = !lean_is_exclusive(v___x_5518_);
if (v_isSharedCheck_5527_ == 0)
{
v___x_5522_ = v___x_5518_;
v_isShared_5523_ = v_isSharedCheck_5527_;
goto v_resetjp_5521_;
}
else
{
lean_inc(v_a_5520_);
lean_dec(v___x_5518_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5527_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v___x_5525_; 
if (v_isShared_5523_ == 0)
{
v___x_5525_ = v___x_5522_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_a_5520_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
}
}
else
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5535_; 
lean_dec(v_anchorInfo_x3f_5483_);
lean_dec(v_a_5480_);
v_a_5528_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5530_ = v___x_5516_;
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5516_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5533_; 
if (v_isShared_5531_ == 0)
{
v___x_5533_ = v___x_5530_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5528_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
return v___x_5533_;
}
}
}
}
else
{
lean_object* v___x_5536_; 
v___x_5536_ = l_Lean_Meta_Grind_casesMatch(v_a_5480_, v___x_5478_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref_known(v___x_5536_, 1);
v_mvarIds_5496_ = v_a_5537_;
goto v___jp_5495_;
}
else
{
lean_object* v_a_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5545_; 
lean_dec(v_anchorInfo_x3f_5483_);
v_a_5538_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5540_ = v___x_5536_;
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_a_5538_);
lean_dec(v___x_5536_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5613_ = _args[0];
lean_object* v_c_5614_ = _args[1];
lean_object* v_a_5615_ = _args[2];
lean_object* v_numCases_5616_ = _args[3];
lean_object* v_isRec_5617_ = _args[4];
lean_object* v_anchorInfo_x3f_5618_ = _args[5];
lean_object* v___y_5619_ = _args[6];
lean_object* v___y_5620_ = _args[7];
lean_object* v___y_5621_ = _args[8];
lean_object* v___y_5622_ = _args[9];
lean_object* v___y_5623_ = _args[10];
lean_object* v___y_5624_ = _args[11];
lean_object* v___y_5625_ = _args[12];
lean_object* v___y_5626_ = _args[13];
lean_object* v___y_5627_ = _args[14];
lean_object* v___y_5628_ = _args[15];
lean_object* v___y_5629_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5630_; lean_object* v_res_5631_; 
v_isRec_boxed_5630_ = lean_unbox(v_isRec_5617_);
v_res_5631_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5613_, v_c_5614_, v_a_5615_, v_numCases_5616_, v_isRec_boxed_5630_, v_anchorInfo_x3f_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec(v___y_5619_);
return v_res_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5632_, uint8_t v_trace_5633_, lean_object* v___f_5634_, lean_object* v_c_5635_, lean_object* v_candidates_x3f_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v___x_5647_; lean_object* v___y_5649_; 
v___x_5647_ = lean_st_mk_ref(v_goal_5632_);
if (v_trace_5633_ == 0)
{
lean_object* v___x_5668_; lean_object* v___x_5669_; 
lean_dec(v_candidates_x3f_5636_);
v___x_5668_ = lean_box(0);
lean_inc(v___x_5647_);
v___x_5669_ = lean_apply_12(v___f_5634_, v___x_5668_, v___x_5647_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, lean_box(0));
v___y_5649_ = v___x_5669_;
goto v___jp_5648_;
}
else
{
lean_object* v___x_5670_; 
v___x_5670_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5635_, v_candidates_x3f_5636_, v___x_5647_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v_a_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; 
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
lean_inc(v_a_5671_);
lean_dec_ref_known(v___x_5670_, 1);
v___x_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5672_, 0, v_a_5671_);
lean_inc(v___x_5647_);
v___x_5673_ = lean_apply_12(v___f_5634_, v___x_5672_, v___x_5647_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, lean_box(0));
v___y_5649_ = v___x_5673_;
goto v___jp_5648_;
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec(v___x_5647_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec(v___y_5639_);
lean_dec_ref(v___y_5638_);
lean_dec(v___y_5637_);
lean_dec_ref(v___f_5634_);
v_a_5674_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5670_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5670_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
v___jp_5648_:
{
if (lean_obj_tag(v___y_5649_) == 0)
{
lean_object* v_a_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5659_; 
v_a_5650_ = lean_ctor_get(v___y_5649_, 0);
v_isSharedCheck_5659_ = !lean_is_exclusive(v___y_5649_);
if (v_isSharedCheck_5659_ == 0)
{
v___x_5652_ = v___y_5649_;
v_isShared_5653_ = v_isSharedCheck_5659_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_a_5650_);
lean_dec(v___y_5649_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5659_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5657_; 
v___x_5654_ = lean_st_ref_get(v___x_5647_);
lean_dec(v___x_5647_);
v___x_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5655_, 0, v_a_5650_);
lean_ctor_set(v___x_5655_, 1, v___x_5654_);
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 0, v___x_5655_);
v___x_5657_ = v___x_5652_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v___x_5655_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
else
{
lean_object* v_a_5660_; lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5667_; 
lean_dec(v___x_5647_);
v_a_5660_ = lean_ctor_get(v___y_5649_, 0);
v_isSharedCheck_5667_ = !lean_is_exclusive(v___y_5649_);
if (v_isSharedCheck_5667_ == 0)
{
v___x_5662_ = v___y_5649_;
v_isShared_5663_ = v_isSharedCheck_5667_;
goto v_resetjp_5661_;
}
else
{
lean_inc(v_a_5660_);
lean_dec(v___y_5649_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5667_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
lean_object* v___x_5665_; 
if (v_isShared_5663_ == 0)
{
v___x_5665_ = v___x_5662_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5660_);
v___x_5665_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
return v___x_5665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5682_, lean_object* v_trace_5683_, lean_object* v___f_5684_, lean_object* v_c_5685_, lean_object* v_candidates_x3f_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_){
_start:
{
uint8_t v_trace_boxed_5697_; lean_object* v_res_5698_; 
v_trace_boxed_5697_ = lean_unbox(v_trace_5683_);
v_res_5698_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5682_, v_trace_boxed_5697_, v___f_5684_, v_c_5685_, v_candidates_x3f_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_);
lean_dec_ref(v_c_5685_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object* v_snd_5699_, lean_object* v_a_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
lean_object* v___x_5711_; 
v___x_5711_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5699_, v___y_5703_);
if (lean_obj_tag(v___x_5711_) == 0)
{
lean_object* v_a_5712_; lean_object* v___x_5713_; 
v_a_5712_ = lean_ctor_get(v___x_5711_, 0);
lean_inc(v_a_5712_);
lean_dec_ref_known(v___x_5711_, 1);
lean_inc(v_a_5700_);
v___x_5713_ = l_Lean_MVarId_getType(v_a_5700_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
if (lean_obj_tag(v___x_5713_) == 0)
{
lean_object* v_a_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v_a_5714_ = lean_ctor_get(v___x_5713_, 0);
lean_inc(v_a_5714_);
lean_dec_ref_known(v___x_5713_, 1);
v___x_5715_ = l_Lean_mkMVar(v_a_5700_);
v___x_5716_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5712_, v___x_5715_, v_a_5714_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
return v___x_5716_;
}
else
{
lean_dec(v_a_5712_);
lean_dec(v_a_5700_);
return v___x_5713_;
}
}
else
{
lean_object* v_a_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5724_; 
lean_dec(v_a_5700_);
v_a_5717_ = lean_ctor_get(v___x_5711_, 0);
v_isSharedCheck_5724_ = !lean_is_exclusive(v___x_5711_);
if (v_isSharedCheck_5724_ == 0)
{
v___x_5719_ = v___x_5711_;
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_a_5717_);
lean_dec(v___x_5711_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5722_; 
if (v_isShared_5720_ == 0)
{
v___x_5722_ = v___x_5719_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5723_; 
v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
v___x_5722_ = v_reuseFailAlloc_5723_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
return v___x_5722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object* v_snd_5725_, lean_object* v_a_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_){
_start:
{
lean_object* v_res_5737_; 
v_res_5737_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(v_snd_5725_, v_a_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_);
lean_dec(v___y_5735_);
lean_dec_ref(v___y_5734_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v_snd_5725_);
return v_res_5737_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; 
v___x_5740_ = lean_box(0);
v___x_5741_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0));
v___x_5742_ = l_Lean_mkConst(v___x_5741_, v___x_5740_);
return v___x_5742_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(lean_object* v___x_5743_, lean_object* v_snd_5744_, lean_object* v___x_5745_, lean_object* v_i_5746_, lean_object* v_falseProof_5747_, lean_object* v_seq_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_){
_start:
{
lean_object* v___x_5759_; lean_object* v_congrThms_5760_; lean_object* v_simp_5761_; lean_object* v_symSimp_5762_; lean_object* v_symDSimp_5763_; lean_object* v_lastTag_5764_; lean_object* v_counters_5765_; lean_object* v_splitDiags_5766_; lean_object* v_ematchDiags_5767_; lean_object* v_lawfulEqCmpMap_5768_; lean_object* v_reflCmpMap_5769_; lean_object* v_anchors_5770_; lean_object* v_fvarAnchors_5771_; lean_object* v_instanceMap_5772_; lean_object* v_hoistedDecls_5773_; lean_object* v_proofInfos_5774_; lean_object* v_numBranches_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5828_; 
v___x_5759_ = lean_st_ref_take(v___y_5751_);
v_congrThms_5760_ = lean_ctor_get(v___x_5759_, 0);
v_simp_5761_ = lean_ctor_get(v___x_5759_, 1);
v_symSimp_5762_ = lean_ctor_get(v___x_5759_, 2);
v_symDSimp_5763_ = lean_ctor_get(v___x_5759_, 3);
v_lastTag_5764_ = lean_ctor_get(v___x_5759_, 4);
v_counters_5765_ = lean_ctor_get(v___x_5759_, 5);
v_splitDiags_5766_ = lean_ctor_get(v___x_5759_, 6);
v_ematchDiags_5767_ = lean_ctor_get(v___x_5759_, 7);
v_lawfulEqCmpMap_5768_ = lean_ctor_get(v___x_5759_, 8);
v_reflCmpMap_5769_ = lean_ctor_get(v___x_5759_, 9);
v_anchors_5770_ = lean_ctor_get(v___x_5759_, 10);
v_fvarAnchors_5771_ = lean_ctor_get(v___x_5759_, 11);
v_instanceMap_5772_ = lean_ctor_get(v___x_5759_, 12);
v_hoistedDecls_5773_ = lean_ctor_get(v___x_5759_, 13);
v_proofInfos_5774_ = lean_ctor_get(v___x_5759_, 14);
v_numBranches_5775_ = lean_ctor_get(v___x_5759_, 15);
v_isSharedCheck_5828_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5777_ = v___x_5759_;
v_isShared_5778_ = v_isSharedCheck_5828_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_numBranches_5775_);
lean_inc(v_proofInfos_5774_);
lean_inc(v_hoistedDecls_5773_);
lean_inc(v_instanceMap_5772_);
lean_inc(v_fvarAnchors_5771_);
lean_inc(v_anchors_5770_);
lean_inc(v_reflCmpMap_5769_);
lean_inc(v_lawfulEqCmpMap_5768_);
lean_inc(v_ematchDiags_5767_);
lean_inc(v_splitDiags_5766_);
lean_inc(v_counters_5765_);
lean_inc(v_lastTag_5764_);
lean_inc(v_symDSimp_5763_);
lean_inc(v_symSimp_5762_);
lean_inc(v_simp_5761_);
lean_inc(v_congrThms_5760_);
lean_dec(v___x_5759_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5828_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5784_; 
v___x_5779_ = lean_unsigned_to_nat(1u);
v___x_5780_ = lean_nat_sub(v___x_5743_, v___x_5779_);
v___x_5781_ = lean_nat_sub(v___x_5780_, v_i_5746_);
lean_dec(v___x_5780_);
v___x_5782_ = lean_nat_sub(v_numBranches_5775_, v___x_5781_);
lean_dec(v___x_5781_);
lean_dec(v_numBranches_5775_);
if (v_isShared_5778_ == 0)
{
lean_ctor_set(v___x_5777_, 15, v___x_5782_);
v___x_5784_ = v___x_5777_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_congrThms_5760_);
lean_ctor_set(v_reuseFailAlloc_5827_, 1, v_simp_5761_);
lean_ctor_set(v_reuseFailAlloc_5827_, 2, v_symSimp_5762_);
lean_ctor_set(v_reuseFailAlloc_5827_, 3, v_symDSimp_5763_);
lean_ctor_set(v_reuseFailAlloc_5827_, 4, v_lastTag_5764_);
lean_ctor_set(v_reuseFailAlloc_5827_, 5, v_counters_5765_);
lean_ctor_set(v_reuseFailAlloc_5827_, 6, v_splitDiags_5766_);
lean_ctor_set(v_reuseFailAlloc_5827_, 7, v_ematchDiags_5767_);
lean_ctor_set(v_reuseFailAlloc_5827_, 8, v_lawfulEqCmpMap_5768_);
lean_ctor_set(v_reuseFailAlloc_5827_, 9, v_reflCmpMap_5769_);
lean_ctor_set(v_reuseFailAlloc_5827_, 10, v_anchors_5770_);
lean_ctor_set(v_reuseFailAlloc_5827_, 11, v_fvarAnchors_5771_);
lean_ctor_set(v_reuseFailAlloc_5827_, 12, v_instanceMap_5772_);
lean_ctor_set(v_reuseFailAlloc_5827_, 13, v_hoistedDecls_5773_);
lean_ctor_set(v_reuseFailAlloc_5827_, 14, v_proofInfos_5774_);
lean_ctor_set(v_reuseFailAlloc_5827_, 15, v___x_5782_);
v___x_5784_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; 
v___x_5785_ = lean_st_ref_put(v___y_5751_, v___x_5784_);
v___x_5786_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5744_, v___y_5751_);
if (lean_obj_tag(v___x_5786_) == 0)
{
lean_object* v_a_5787_; lean_object* v_mvarId_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; 
v_a_5787_ = lean_ctor_get(v___x_5786_, 0);
lean_inc(v_a_5787_);
lean_dec_ref_known(v___x_5786_, 1);
v_mvarId_5788_ = lean_ctor_get(v_snd_5744_, 1);
lean_inc(v_mvarId_5788_);
lean_dec_ref(v_snd_5744_);
v___x_5789_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_5790_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkHoistedDecls___boxed), 13, 3);
lean_closure_set(v___x_5790_, 0, v_a_5787_);
lean_closure_set(v___x_5790_, 1, v_falseProof_5747_);
lean_closure_set(v___x_5790_, 2, v___x_5789_);
v___x_5791_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5788_, v___x_5790_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_);
if (lean_obj_tag(v___x_5791_) == 0)
{
lean_object* v_a_5792_; lean_object* v___x_5793_; 
v_a_5792_ = lean_ctor_get(v___x_5791_, 0);
lean_inc(v_a_5792_);
lean_dec_ref_known(v___x_5791_, 1);
v___x_5793_ = l_Lean_MVarId_assignFalseProof(v___x_5745_, v_a_5792_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v___x_5795_; uint8_t v_isShared_5796_; uint8_t v_isSharedCheck_5801_; 
v_isSharedCheck_5801_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5801_ == 0)
{
lean_object* v_unused_5802_; 
v_unused_5802_ = lean_ctor_get(v___x_5793_, 0);
lean_dec(v_unused_5802_);
v___x_5795_ = v___x_5793_;
v_isShared_5796_ = v_isSharedCheck_5801_;
goto v_resetjp_5794_;
}
else
{
lean_dec(v___x_5793_);
v___x_5795_ = lean_box(0);
v_isShared_5796_ = v_isSharedCheck_5801_;
goto v_resetjp_5794_;
}
v_resetjp_5794_:
{
lean_object* v___x_5797_; lean_object* v___x_5799_; 
v___x_5797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5797_, 0, v_seq_5748_);
if (v_isShared_5796_ == 0)
{
lean_ctor_set(v___x_5795_, 0, v___x_5797_);
v___x_5799_ = v___x_5795_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v___x_5797_);
v___x_5799_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
return v___x_5799_;
}
}
}
else
{
lean_object* v_a_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5810_; 
lean_dec(v_seq_5748_);
v_a_5803_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5810_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5810_ == 0)
{
v___x_5805_ = v___x_5793_;
v_isShared_5806_ = v_isSharedCheck_5810_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_a_5803_);
lean_dec(v___x_5793_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5810_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v___x_5808_; 
if (v_isShared_5806_ == 0)
{
v___x_5808_ = v___x_5805_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_a_5803_);
v___x_5808_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
return v___x_5808_;
}
}
}
}
else
{
lean_object* v_a_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5818_; 
lean_dec(v_seq_5748_);
lean_dec(v___x_5745_);
v_a_5811_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5818_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5818_ == 0)
{
v___x_5813_ = v___x_5791_;
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_a_5811_);
lean_dec(v___x_5791_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5816_; 
if (v_isShared_5814_ == 0)
{
v___x_5816_ = v___x_5813_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
}
}
}
}
else
{
lean_object* v_a_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5826_; 
lean_dec(v_seq_5748_);
lean_dec_ref(v_falseProof_5747_);
lean_dec(v___x_5745_);
lean_dec_ref(v_snd_5744_);
v_a_5819_ = lean_ctor_get(v___x_5786_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v___x_5786_);
if (v_isSharedCheck_5826_ == 0)
{
v___x_5821_ = v___x_5786_;
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_a_5819_);
lean_dec(v___x_5786_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5824_; 
if (v_isShared_5822_ == 0)
{
v___x_5824_ = v___x_5821_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5819_);
v___x_5824_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
return v___x_5824_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___boxed(lean_object* v___x_5829_, lean_object* v_snd_5830_, lean_object* v___x_5831_, lean_object* v_i_5832_, lean_object* v_falseProof_5833_, lean_object* v_seq_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_){
_start:
{
lean_object* v_res_5845_; 
v_res_5845_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5829_, v_snd_5830_, v___x_5831_, v_i_5832_, v_falseProof_5833_, v_seq_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
lean_dec(v___y_5843_);
lean_dec_ref(v___y_5842_);
lean_dec(v___y_5841_);
lean_dec_ref(v___y_5840_);
lean_dec(v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec(v___y_5837_);
lean_dec_ref(v___y_5836_);
lean_dec(v___y_5835_);
lean_dec(v_i_5832_);
lean_dec(v___x_5829_);
return v_res_5845_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v___x_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_){
_start:
{
if (lean_obj_tag(v_a_5847_) == 0)
{
lean_object* v___x_5849_; 
v___x_5849_ = l_List_reverse___redArg(v_a_5848_);
return v___x_5849_;
}
else
{
lean_object* v_head_5850_; lean_object* v_toGoalState_5851_; lean_object* v_tail_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5901_; 
v_head_5850_ = lean_ctor_get(v_a_5847_, 0);
lean_inc(v_head_5850_);
v_toGoalState_5851_ = lean_ctor_get(v_head_5850_, 0);
lean_inc_ref(v_toGoalState_5851_);
v_tail_5852_ = lean_ctor_get(v_a_5847_, 1);
v_isSharedCheck_5901_ = !lean_is_exclusive(v_a_5847_);
if (v_isSharedCheck_5901_ == 0)
{
lean_object* v_unused_5902_; 
v_unused_5902_ = lean_ctor_get(v_a_5847_, 0);
lean_dec(v_unused_5902_);
v___x_5854_ = v_a_5847_;
v_isShared_5855_ = v_isSharedCheck_5901_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_tail_5852_);
lean_dec(v_a_5847_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5901_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v_mvarId_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5899_; 
v_mvarId_5856_ = lean_ctor_get(v_head_5850_, 1);
v_isSharedCheck_5899_ = !lean_is_exclusive(v_head_5850_);
if (v_isSharedCheck_5899_ == 0)
{
lean_object* v_unused_5900_; 
v_unused_5900_ = lean_ctor_get(v_head_5850_, 0);
lean_dec(v_unused_5900_);
v___x_5858_ = v_head_5850_;
v_isShared_5859_ = v_isSharedCheck_5899_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_mvarId_5856_);
lean_dec(v_head_5850_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5899_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v_nextDeclIdx_5860_; lean_object* v_enodeMap_5861_; lean_object* v_exprs_5862_; lean_object* v_parents_5863_; lean_object* v_congrTable_5864_; lean_object* v_appMap_5865_; lean_object* v_indicesFound_5866_; lean_object* v_toProcess_5867_; lean_object* v_internalizing_5868_; uint8_t v_inconsistent_5869_; lean_object* v_nextIdx_5870_; lean_object* v_newRawFacts_5871_; lean_object* v_facts_5872_; lean_object* v_extThms_5873_; lean_object* v_ematch_5874_; lean_object* v_inj_5875_; lean_object* v_split_5876_; lean_object* v_clean_5877_; lean_object* v_sstates_5878_; lean_object* v_goalStack_5879_; uint64_t v_introBase_5880_; lean_object* v_numIntros_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_5898_; 
v_nextDeclIdx_5860_ = lean_ctor_get(v_toGoalState_5851_, 0);
v_enodeMap_5861_ = lean_ctor_get(v_toGoalState_5851_, 1);
v_exprs_5862_ = lean_ctor_get(v_toGoalState_5851_, 2);
v_parents_5863_ = lean_ctor_get(v_toGoalState_5851_, 3);
v_congrTable_5864_ = lean_ctor_get(v_toGoalState_5851_, 4);
v_appMap_5865_ = lean_ctor_get(v_toGoalState_5851_, 5);
v_indicesFound_5866_ = lean_ctor_get(v_toGoalState_5851_, 6);
v_toProcess_5867_ = lean_ctor_get(v_toGoalState_5851_, 7);
v_internalizing_5868_ = lean_ctor_get(v_toGoalState_5851_, 8);
v_inconsistent_5869_ = lean_ctor_get_uint8(v_toGoalState_5851_, sizeof(void*)*20 + 8);
v_nextIdx_5870_ = lean_ctor_get(v_toGoalState_5851_, 9);
v_newRawFacts_5871_ = lean_ctor_get(v_toGoalState_5851_, 10);
v_facts_5872_ = lean_ctor_get(v_toGoalState_5851_, 11);
v_extThms_5873_ = lean_ctor_get(v_toGoalState_5851_, 12);
v_ematch_5874_ = lean_ctor_get(v_toGoalState_5851_, 13);
v_inj_5875_ = lean_ctor_get(v_toGoalState_5851_, 14);
v_split_5876_ = lean_ctor_get(v_toGoalState_5851_, 15);
v_clean_5877_ = lean_ctor_get(v_toGoalState_5851_, 16);
v_sstates_5878_ = lean_ctor_get(v_toGoalState_5851_, 17);
v_goalStack_5879_ = lean_ctor_get(v_toGoalState_5851_, 18);
v_introBase_5880_ = lean_ctor_get_uint64(v_toGoalState_5851_, sizeof(void*)*20);
v_numIntros_5881_ = lean_ctor_get(v_toGoalState_5851_, 19);
v_isSharedCheck_5898_ = !lean_is_exclusive(v_toGoalState_5851_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5883_ = v_toGoalState_5851_;
v_isShared_5884_ = v_isSharedCheck_5898_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_numIntros_5881_);
lean_inc(v_goalStack_5879_);
lean_inc(v_sstates_5878_);
lean_inc(v_clean_5877_);
lean_inc(v_split_5876_);
lean_inc(v_inj_5875_);
lean_inc(v_ematch_5874_);
lean_inc(v_extThms_5873_);
lean_inc(v_facts_5872_);
lean_inc(v_newRawFacts_5871_);
lean_inc(v_nextIdx_5870_);
lean_inc(v_internalizing_5868_);
lean_inc(v_toProcess_5867_);
lean_inc(v_indicesFound_5866_);
lean_inc(v_appMap_5865_);
lean_inc(v_congrTable_5864_);
lean_inc(v_parents_5863_);
lean_inc(v_exprs_5862_);
lean_inc(v_enodeMap_5861_);
lean_inc(v_nextDeclIdx_5860_);
lean_dec(v_toGoalState_5851_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_5898_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5889_; 
v___x_5885_ = lean_unsigned_to_nat(0u);
v___x_5886_ = lean_array_get_size(v___x_5846_);
v___x_5887_ = l_Array_extract___redArg(v_goalStack_5879_, v___x_5885_, v___x_5886_);
lean_dec_ref(v_goalStack_5879_);
if (v_isShared_5884_ == 0)
{
lean_ctor_set(v___x_5883_, 18, v___x_5887_);
v___x_5889_ = v___x_5883_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_nextDeclIdx_5860_);
lean_ctor_set(v_reuseFailAlloc_5897_, 1, v_enodeMap_5861_);
lean_ctor_set(v_reuseFailAlloc_5897_, 2, v_exprs_5862_);
lean_ctor_set(v_reuseFailAlloc_5897_, 3, v_parents_5863_);
lean_ctor_set(v_reuseFailAlloc_5897_, 4, v_congrTable_5864_);
lean_ctor_set(v_reuseFailAlloc_5897_, 5, v_appMap_5865_);
lean_ctor_set(v_reuseFailAlloc_5897_, 6, v_indicesFound_5866_);
lean_ctor_set(v_reuseFailAlloc_5897_, 7, v_toProcess_5867_);
lean_ctor_set(v_reuseFailAlloc_5897_, 8, v_internalizing_5868_);
lean_ctor_set(v_reuseFailAlloc_5897_, 9, v_nextIdx_5870_);
lean_ctor_set(v_reuseFailAlloc_5897_, 10, v_newRawFacts_5871_);
lean_ctor_set(v_reuseFailAlloc_5897_, 11, v_facts_5872_);
lean_ctor_set(v_reuseFailAlloc_5897_, 12, v_extThms_5873_);
lean_ctor_set(v_reuseFailAlloc_5897_, 13, v_ematch_5874_);
lean_ctor_set(v_reuseFailAlloc_5897_, 14, v_inj_5875_);
lean_ctor_set(v_reuseFailAlloc_5897_, 15, v_split_5876_);
lean_ctor_set(v_reuseFailAlloc_5897_, 16, v_clean_5877_);
lean_ctor_set(v_reuseFailAlloc_5897_, 17, v_sstates_5878_);
lean_ctor_set(v_reuseFailAlloc_5897_, 18, v___x_5887_);
lean_ctor_set(v_reuseFailAlloc_5897_, 19, v_numIntros_5881_);
lean_ctor_set_uint8(v_reuseFailAlloc_5897_, sizeof(void*)*20 + 8, v_inconsistent_5869_);
lean_ctor_set_uint64(v_reuseFailAlloc_5897_, sizeof(void*)*20, v_introBase_5880_);
v___x_5889_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
lean_object* v___x_5891_; 
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 0, v___x_5889_);
v___x_5891_ = v___x_5858_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v___x_5889_);
lean_ctor_set(v_reuseFailAlloc_5896_, 1, v_mvarId_5856_);
v___x_5891_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
lean_object* v___x_5893_; 
if (v_isShared_5855_ == 0)
{
lean_ctor_set(v___x_5854_, 1, v_a_5848_);
lean_ctor_set(v___x_5854_, 0, v___x_5891_);
v___x_5893_ = v___x_5854_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5891_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_a_5848_);
v___x_5893_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
v_a_5847_ = v_tail_5852_;
v_a_5848_ = v___x_5893_;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v___x_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5903_, v_a_5904_, v_a_5905_);
lean_dec_ref(v___x_5903_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(lean_object* v___x_5907_, lean_object* v_gs_5908_){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5909_ = lean_box(0);
v___x_5910_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5907_, v_gs_5908_, v___x_5909_);
return v___x_5910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0___boxed(lean_object* v___x_5911_, lean_object* v_gs_5912_){
_start:
{
lean_object* v_res_5913_; 
v_res_5913_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5911_, v_gs_5912_);
lean_dec_ref(v___x_5911_);
return v_res_5913_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5914_, lean_object* v_a_5915_, lean_object* v_goal_5916_, lean_object* v___x_5917_, lean_object* v_snd_5918_, lean_object* v___x_5919_, uint8_t v_stopAtFirstFailure_5920_, lean_object* v___x_5921_, lean_object* v_as_x27_5922_, lean_object* v_b_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_){
_start:
{
if (lean_obj_tag(v_as_x27_5922_) == 0)
{
lean_object* v___x_5934_; 
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v___x_5934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5934_, 0, v_b_5923_);
return v___x_5934_;
}
else
{
lean_object* v_snd_5935_; lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_6216_; 
v_snd_5935_ = lean_ctor_get(v_b_5923_, 1);
v_isSharedCheck_6216_ = !lean_is_exclusive(v_b_5923_);
if (v_isSharedCheck_6216_ == 0)
{
lean_object* v_unused_6217_; 
v_unused_6217_ = lean_ctor_get(v_b_5923_, 0);
lean_dec(v_unused_6217_);
v___x_5937_ = v_b_5923_;
v_isShared_5938_ = v_isSharedCheck_6216_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_snd_5935_);
lean_dec(v_b_5923_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_6216_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v_snd_5939_; lean_object* v_snd_5940_; lean_object* v_snd_5941_; lean_object* v_head_5942_; lean_object* v_tail_5943_; lean_object* v_fst_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_6214_; 
v_snd_5939_ = lean_ctor_get(v_snd_5935_, 1);
lean_inc(v_snd_5939_);
v_snd_5940_ = lean_ctor_get(v_snd_5939_, 1);
lean_inc(v_snd_5940_);
v_snd_5941_ = lean_ctor_get(v_snd_5940_, 1);
lean_inc(v_snd_5941_);
v_head_5942_ = lean_ctor_get(v_as_x27_5922_, 0);
v_tail_5943_ = lean_ctor_get(v_as_x27_5922_, 1);
v_fst_5944_ = lean_ctor_get(v_snd_5935_, 0);
v_isSharedCheck_6214_ = !lean_is_exclusive(v_snd_5935_);
if (v_isSharedCheck_6214_ == 0)
{
lean_object* v_unused_6215_; 
v_unused_6215_ = lean_ctor_get(v_snd_5935_, 1);
lean_dec(v_unused_6215_);
v___x_5946_ = v_snd_5935_;
v_isShared_5947_ = v_isSharedCheck_6214_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_fst_5944_);
lean_dec(v_snd_5935_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_6214_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v_fst_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_6212_; 
v_fst_5948_ = lean_ctor_get(v_snd_5939_, 0);
v_isSharedCheck_6212_ = !lean_is_exclusive(v_snd_5939_);
if (v_isSharedCheck_6212_ == 0)
{
lean_object* v_unused_6213_; 
v_unused_6213_ = lean_ctor_get(v_snd_5939_, 1);
lean_dec(v_unused_6213_);
v___x_5950_ = v_snd_5939_;
v_isShared_5951_ = v_isSharedCheck_6212_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_fst_5948_);
lean_dec(v_snd_5939_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_6212_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v_fst_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_6210_; 
v_fst_5952_ = lean_ctor_get(v_snd_5940_, 0);
v_isSharedCheck_6210_ = !lean_is_exclusive(v_snd_5940_);
if (v_isSharedCheck_6210_ == 0)
{
lean_object* v_unused_6211_; 
v_unused_6211_ = lean_ctor_get(v_snd_5940_, 1);
lean_dec(v_unused_6211_);
v___x_5954_ = v_snd_5940_;
v_isShared_5955_ = v_isSharedCheck_6210_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_fst_5952_);
lean_dec(v_snd_5940_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_6210_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v_start_5956_; lean_object* v_stop_5957_; lean_object* v_step_5958_; lean_object* v___x_5959_; uint8_t v___x_5960_; 
v_start_5956_ = lean_ctor_get(v_snd_5941_, 0);
v_stop_5957_ = lean_ctor_get(v_snd_5941_, 1);
v_step_5958_ = lean_ctor_get(v_snd_5941_, 2);
v___x_5959_ = lean_box(0);
v___x_5960_ = lean_nat_dec_lt(v_start_5956_, v_stop_5957_);
if (v___x_5960_ == 0)
{
lean_object* v___x_5962_; 
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
if (v_isShared_5955_ == 0)
{
v___x_5962_ = v___x_5954_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_5973_, 1, v_snd_5941_);
v___x_5962_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
lean_object* v___x_5964_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 1, v___x_5962_);
v___x_5964_ = v___x_5950_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_fst_5948_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___x_5962_);
v___x_5964_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
lean_object* v___x_5966_; 
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v___x_5964_);
v___x_5966_ = v___x_5946_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___x_5964_);
v___x_5966_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_object* v___x_5968_; 
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 1, v___x_5966_);
lean_ctor_set(v___x_5937_, 0, v___x_5959_);
v___x_5968_ = v___x_5937_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v___x_5959_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v___x_5966_);
v___x_5968_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5969_; 
v___x_5969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
return v___x_5969_;
}
}
}
}
}
else
{
lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_6206_; 
lean_inc(v_step_5958_);
lean_inc(v_stop_5957_);
lean_inc(v_start_5956_);
v_isSharedCheck_6206_ = !lean_is_exclusive(v_snd_5941_);
if (v_isSharedCheck_6206_ == 0)
{
lean_object* v_unused_6207_; lean_object* v_unused_6208_; lean_object* v_unused_6209_; 
v_unused_6207_ = lean_ctor_get(v_snd_5941_, 2);
lean_dec(v_unused_6207_);
v_unused_6208_ = lean_ctor_get(v_snd_5941_, 1);
lean_dec(v_unused_6208_);
v_unused_6209_ = lean_ctor_get(v_snd_5941_, 0);
lean_dec(v_unused_6209_);
v___x_5975_ = v_snd_5941_;
v_isShared_5976_ = v_isSharedCheck_6206_;
goto v_resetjp_5974_;
}
else
{
lean_dec(v_snd_5941_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_6206_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5977_; lean_object* v___x_5979_; 
v___x_5977_ = lean_nat_add(v_start_5956_, v_step_5958_);
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 0, v___x_5977_);
v___x_5979_ = v___x_5975_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_6205_; 
v_reuseFailAlloc_6205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6205_, 0, v___x_5977_);
lean_ctor_set(v_reuseFailAlloc_6205_, 1, v_stop_5957_);
lean_ctor_set(v_reuseFailAlloc_6205_, 2, v_step_5958_);
v___x_5979_ = v_reuseFailAlloc_6205_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
lean_object* v___x_5980_; 
lean_inc_ref(v_kp_5914_);
lean_inc(v___y_5932_);
lean_inc_ref(v___y_5931_);
lean_inc(v___y_5930_);
lean_inc_ref(v___y_5929_);
lean_inc(v___y_5928_);
lean_inc_ref(v___y_5927_);
lean_inc(v___y_5926_);
lean_inc_ref(v___y_5925_);
lean_inc(v___y_5924_);
lean_inc(v_head_5942_);
v___x_5980_ = lean_apply_11(v_kp_5914_, v_head_5942_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, lean_box(0));
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_object* v_a_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_6196_; 
v_a_5981_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_6196_ == 0)
{
v___x_5983_ = v___x_5980_;
v_isShared_5984_ = v_isSharedCheck_6196_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_a_5981_);
lean_dec(v___x_5980_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_6196_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
if (lean_obj_tag(v_a_5981_) == 0)
{
lean_object* v_seq_5985_; lean_object* v_ncb_x3f_5987_; lean_object* v_mvarId_6016_; lean_object* v___x_6017_; 
lean_del_object(v___x_5983_);
v_seq_5985_ = lean_ctor_get(v_a_5981_, 0);
lean_inc(v_seq_5985_);
lean_dec_ref_known(v_a_5981_, 1);
v_mvarId_6016_ = lean_ctor_get(v_head_5942_, 1);
lean_inc(v_mvarId_6016_);
v___x_6017_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_6016_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
if (lean_obj_tag(v___x_6017_) == 0)
{
lean_object* v_a_6018_; 
v_a_6018_ = lean_ctor_get(v___x_6017_, 0);
lean_inc(v_a_6018_);
lean_dec_ref_known(v___x_6017_, 1);
if (lean_obj_tag(v_a_6018_) == 1)
{
lean_object* v_val_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6074_; 
v_val_6019_ = lean_ctor_get(v_a_6018_, 0);
v_isSharedCheck_6074_ = !lean_is_exclusive(v_a_6018_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6021_ = v_a_6018_;
v_isShared_6022_ = v_isSharedCheck_6074_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_val_6019_);
lean_dec(v_a_6018_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6074_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
lean_object* v___x_6023_; 
lean_inc(v_seq_5985_);
lean_inc_ref(v_goal_5916_);
lean_inc(v_a_5915_);
v___x_6023_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_5915_, v_goal_5916_, v_seq_5985_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
if (lean_obj_tag(v___x_6023_) == 0)
{
lean_object* v_a_6024_; uint8_t v___x_6025_; 
v_a_6024_ = lean_ctor_get(v___x_6023_, 0);
lean_inc(v_a_6024_);
lean_dec_ref_known(v___x_6023_, 1);
v___x_6025_ = lean_unbox(v_a_6024_);
lean_dec(v_a_6024_);
if (v___x_6025_ == 0)
{
if (lean_obj_tag(v_fst_5952_) == 0)
{
lean_object* v___x_6026_; 
v___x_6026_ = l_Lean_Meta_Grind_saveState___redArg(v___y_5926_, v___y_5930_, v___y_5932_);
if (lean_obj_tag(v___x_6026_) == 0)
{
lean_object* v_a_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6032_; 
v_a_6027_ = lean_ctor_get(v___x_6026_, 0);
lean_inc(v_a_6027_);
lean_dec_ref_known(v___x_6026_, 1);
lean_inc(v_seq_5985_);
v___x_6028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6028_, 0, v_val_6019_);
lean_ctor_set(v___x_6028_, 1, v_seq_5985_);
v___x_6029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6029_, 0, v_start_5956_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6030_, 0, v_a_6027_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
if (v_isShared_6022_ == 0)
{
lean_ctor_set(v___x_6021_, 0, v___x_6030_);
v___x_6032_ = v___x_6021_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_6030_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
v_ncb_x3f_5987_ = v___x_6032_;
goto v___jp_5986_;
}
}
else
{
lean_object* v_a_6034_; lean_object* v___x_6036_; uint8_t v_isShared_6037_; uint8_t v_isSharedCheck_6041_; 
lean_del_object(v___x_6021_);
lean_dec(v_val_6019_);
lean_dec(v_seq_5985_);
lean_dec_ref(v___x_5979_);
lean_dec(v_start_5956_);
lean_del_object(v___x_5954_);
lean_del_object(v___x_5950_);
lean_dec(v_fst_5948_);
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5937_);
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v_a_6034_ = lean_ctor_get(v___x_6026_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v___x_6026_);
if (v_isSharedCheck_6041_ == 0)
{
v___x_6036_ = v___x_6026_;
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
else
{
lean_inc(v_a_6034_);
lean_dec(v___x_6026_);
v___x_6036_ = lean_box(0);
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
v_resetjp_6035_:
{
lean_object* v___x_6039_; 
if (v_isShared_6037_ == 0)
{
v___x_6039_ = v___x_6036_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v_a_6034_);
v___x_6039_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
return v___x_6039_;
}
}
}
}
else
{
lean_del_object(v___x_6021_);
lean_dec(v_val_6019_);
lean_dec(v_start_5956_);
v_ncb_x3f_5987_ = v_fst_5952_;
goto v___jp_5986_;
}
}
else
{
lean_object* v___x_6042_; 
lean_del_object(v___x_5954_);
lean_del_object(v___x_5950_);
lean_del_object(v___x_5946_);
lean_del_object(v___x_5937_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v___x_6042_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5917_, v_snd_5918_, v___x_5919_, v_start_5956_, v_val_6019_, v_seq_5985_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
lean_dec(v_start_5956_);
if (lean_obj_tag(v___x_6042_) == 0)
{
lean_object* v_a_6043_; lean_object* v___x_6045_; uint8_t v_isShared_6046_; uint8_t v_isSharedCheck_6057_; 
v_a_6043_ = lean_ctor_get(v___x_6042_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6042_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6045_ = v___x_6042_;
v_isShared_6046_ = v_isSharedCheck_6057_;
goto v_resetjp_6044_;
}
else
{
lean_inc(v_a_6043_);
lean_dec(v___x_6042_);
v___x_6045_ = lean_box(0);
v_isShared_6046_ = v_isSharedCheck_6057_;
goto v_resetjp_6044_;
}
v_resetjp_6044_:
{
lean_object* v___x_6048_; 
if (v_isShared_6022_ == 0)
{
lean_ctor_set(v___x_6021_, 0, v_a_6043_);
v___x_6048_ = v___x_6021_;
goto v_reusejp_6047_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6043_);
v___x_6048_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6054_; 
v___x_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6049_, 0, v_fst_5952_);
lean_ctor_set(v___x_6049_, 1, v___x_5979_);
v___x_6050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6050_, 0, v_fst_5948_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6051_, 0, v_fst_5944_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6048_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
if (v_isShared_6046_ == 0)
{
lean_ctor_set(v___x_6045_, 0, v___x_6052_);
v___x_6054_ = v___x_6045_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6052_);
v___x_6054_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
return v___x_6054_;
}
}
}
}
else
{
lean_object* v_a_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6065_; 
lean_del_object(v___x_6021_);
lean_dec_ref(v___x_5979_);
lean_dec(v_fst_5952_);
lean_dec(v_fst_5948_);
lean_dec(v_fst_5944_);
v_a_6058_ = lean_ctor_get(v___x_6042_, 0);
v_isSharedCheck_6065_ = !lean_is_exclusive(v___x_6042_);
if (v_isSharedCheck_6065_ == 0)
{
v___x_6060_ = v___x_6042_;
v_isShared_6061_ = v_isSharedCheck_6065_;
goto v_resetjp_6059_;
}
else
{
lean_inc(v_a_6058_);
lean_dec(v___x_6042_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6065_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
lean_object* v___x_6063_; 
if (v_isShared_6061_ == 0)
{
v___x_6063_ = v___x_6060_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
v___x_6063_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
return v___x_6063_;
}
}
}
}
}
else
{
lean_object* v_a_6066_; lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6073_; 
lean_del_object(v___x_6021_);
lean_dec(v_val_6019_);
lean_dec(v_seq_5985_);
lean_dec_ref(v___x_5979_);
lean_dec(v_start_5956_);
lean_del_object(v___x_5954_);
lean_dec(v_fst_5952_);
lean_del_object(v___x_5950_);
lean_dec(v_fst_5948_);
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5937_);
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v_a_6066_ = lean_ctor_get(v___x_6023_, 0);
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6073_ == 0)
{
v___x_6068_ = v___x_6023_;
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
else
{
lean_inc(v_a_6066_);
lean_dec(v___x_6023_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6071_; 
if (v_isShared_6069_ == 0)
{
v___x_6071_ = v___x_6068_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
v___x_6071_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
return v___x_6071_;
}
}
}
}
}
else
{
uint8_t v___x_6075_; 
lean_dec(v_a_6018_);
lean_dec(v_start_5956_);
lean_del_object(v___x_5954_);
lean_del_object(v___x_5950_);
lean_del_object(v___x_5946_);
lean_del_object(v___x_5937_);
v___x_6075_ = l_List_isEmpty___redArg(v_seq_5985_);
if (v___x_6075_ == 0)
{
lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; 
v___x_6076_ = lean_array_push(v_fst_5944_, v_seq_5985_);
v___x_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6077_, 0, v_fst_5952_);
lean_ctor_set(v___x_6077_, 1, v___x_5979_);
v___x_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6078_, 0, v_fst_5948_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6076_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___x_6080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_5959_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v_as_x27_5922_ = v_tail_5943_;
v_b_5923_ = v___x_6080_;
goto _start;
}
else
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; 
lean_dec(v_seq_5985_);
v___x_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6082_, 0, v_fst_5952_);
lean_ctor_set(v___x_6082_, 1, v___x_5979_);
v___x_6083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6083_, 0, v_fst_5948_);
lean_ctor_set(v___x_6083_, 1, v___x_6082_);
v___x_6084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6084_, 0, v_fst_5944_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_5959_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v_as_x27_5922_ = v_tail_5943_;
v_b_5923_ = v___x_6085_;
goto _start;
}
}
}
else
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6094_; 
lean_dec(v_seq_5985_);
lean_dec_ref(v___x_5979_);
lean_dec(v_start_5956_);
lean_del_object(v___x_5954_);
lean_dec(v_fst_5952_);
lean_del_object(v___x_5950_);
lean_dec(v_fst_5948_);
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5937_);
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v_a_6087_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6089_ = v___x_6017_;
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v___x_6017_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6092_; 
if (v_isShared_6090_ == 0)
{
v___x_6092_ = v___x_6089_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_a_6087_);
v___x_6092_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
return v___x_6092_;
}
}
}
v___jp_5986_:
{
uint8_t v___x_5988_; 
v___x_5988_ = l_List_isEmpty___redArg(v_seq_5985_);
if (v___x_5988_ == 0)
{
lean_object* v___x_5989_; lean_object* v___x_5991_; 
v___x_5989_ = lean_array_push(v_fst_5944_, v_seq_5985_);
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5979_);
lean_ctor_set(v___x_5954_, 0, v_ncb_x3f_5987_);
v___x_5991_ = v___x_5954_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_ncb_x3f_5987_);
lean_ctor_set(v_reuseFailAlloc_6002_, 1, v___x_5979_);
v___x_5991_ = v_reuseFailAlloc_6002_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
lean_object* v___x_5993_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 1, v___x_5991_);
v___x_5993_ = v___x_5950_;
goto v_reusejp_5992_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v_fst_5948_);
lean_ctor_set(v_reuseFailAlloc_6001_, 1, v___x_5991_);
v___x_5993_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5992_;
}
v_reusejp_5992_:
{
lean_object* v___x_5995_; 
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v___x_5993_);
lean_ctor_set(v___x_5946_, 0, v___x_5989_);
v___x_5995_ = v___x_5946_;
goto v_reusejp_5994_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v___x_5989_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v___x_5993_);
v___x_5995_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5994_;
}
v_reusejp_5994_:
{
lean_object* v___x_5997_; 
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 1, v___x_5995_);
lean_ctor_set(v___x_5937_, 0, v___x_5959_);
v___x_5997_ = v___x_5937_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v___x_5959_);
lean_ctor_set(v_reuseFailAlloc_5999_, 1, v___x_5995_);
v___x_5997_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
v_as_x27_5922_ = v_tail_5943_;
v_b_5923_ = v___x_5997_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_6004_; 
lean_dec(v_seq_5985_);
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5979_);
lean_ctor_set(v___x_5954_, 0, v_ncb_x3f_5987_);
v___x_6004_ = v___x_5954_;
goto v_reusejp_6003_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_ncb_x3f_5987_);
lean_ctor_set(v_reuseFailAlloc_6015_, 1, v___x_5979_);
v___x_6004_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6003_;
}
v_reusejp_6003_:
{
lean_object* v___x_6006_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 1, v___x_6004_);
v___x_6006_ = v___x_5950_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v_fst_5948_);
lean_ctor_set(v_reuseFailAlloc_6014_, 1, v___x_6004_);
v___x_6006_ = v_reuseFailAlloc_6014_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
lean_object* v___x_6008_; 
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v___x_6006_);
v___x_6008_ = v___x_5946_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v___x_6006_);
v___x_6008_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
lean_object* v___x_6010_; 
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 1, v___x_6008_);
lean_ctor_set(v___x_5937_, 0, v___x_5959_);
v___x_6010_ = v___x_5937_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_5959_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___x_6008_);
v___x_6010_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
v_as_x27_5922_ = v_tail_5943_;
v_b_5923_ = v___x_6010_;
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
lean_dec(v_start_5956_);
if (lean_obj_tag(v_fst_5952_) == 1)
{
lean_object* v_val_6095_; lean_object* v_snd_6096_; lean_object* v_snd_6097_; lean_object* v_fst_6098_; lean_object* v___x_6100_; uint8_t v_isShared_6101_; uint8_t v_isSharedCheck_6153_; 
lean_dec_ref_known(v_a_5981_, 1);
lean_del_object(v___x_5983_);
lean_del_object(v___x_5950_);
lean_del_object(v___x_5946_);
lean_del_object(v___x_5937_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v_val_6095_ = lean_ctor_get(v_fst_5952_, 0);
lean_inc(v_val_6095_);
v_snd_6096_ = lean_ctor_get(v_val_6095_, 1);
lean_inc(v_snd_6096_);
v_snd_6097_ = lean_ctor_get(v_snd_6096_, 1);
lean_inc(v_snd_6097_);
v_fst_6098_ = lean_ctor_get(v_val_6095_, 0);
v_isSharedCheck_6153_ = !lean_is_exclusive(v_val_6095_);
if (v_isSharedCheck_6153_ == 0)
{
lean_object* v_unused_6154_; 
v_unused_6154_ = lean_ctor_get(v_val_6095_, 1);
lean_dec(v_unused_6154_);
v___x_6100_ = v_val_6095_;
v_isShared_6101_ = v_isSharedCheck_6153_;
goto v_resetjp_6099_;
}
else
{
lean_inc(v_fst_6098_);
lean_dec(v_val_6095_);
v___x_6100_ = lean_box(0);
v_isShared_6101_ = v_isSharedCheck_6153_;
goto v_resetjp_6099_;
}
v_resetjp_6099_:
{
lean_object* v_fst_6102_; lean_object* v___x_6104_; uint8_t v_isShared_6105_; uint8_t v_isSharedCheck_6151_; 
v_fst_6102_ = lean_ctor_get(v_snd_6096_, 0);
v_isSharedCheck_6151_ = !lean_is_exclusive(v_snd_6096_);
if (v_isSharedCheck_6151_ == 0)
{
lean_object* v_unused_6152_; 
v_unused_6152_ = lean_ctor_get(v_snd_6096_, 1);
lean_dec(v_unused_6152_);
v___x_6104_ = v_snd_6096_;
v_isShared_6105_ = v_isSharedCheck_6151_;
goto v_resetjp_6103_;
}
else
{
lean_inc(v_fst_6102_);
lean_dec(v_snd_6096_);
v___x_6104_ = lean_box(0);
v_isShared_6105_ = v_isSharedCheck_6151_;
goto v_resetjp_6103_;
}
v_resetjp_6103_:
{
lean_object* v_fst_6106_; lean_object* v_snd_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6150_; 
v_fst_6106_ = lean_ctor_get(v_snd_6097_, 0);
v_snd_6107_ = lean_ctor_get(v_snd_6097_, 1);
v_isSharedCheck_6150_ = !lean_is_exclusive(v_snd_6097_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6109_ = v_snd_6097_;
v_isShared_6110_ = v_isSharedCheck_6150_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_snd_6107_);
lean_inc(v_fst_6106_);
lean_dec(v_snd_6097_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6150_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6111_; 
v___x_6111_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_fst_6098_, v___y_5926_, v___y_5930_, v___y_5932_);
if (lean_obj_tag(v___x_6111_) == 0)
{
lean_object* v___x_6112_; 
lean_dec_ref_known(v___x_6111_, 1);
v___x_6112_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5917_, v_snd_5918_, v___x_5919_, v_fst_6102_, v_fst_6106_, v_snd_6107_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
lean_dec(v_fst_6102_);
if (lean_obj_tag(v___x_6112_) == 0)
{
lean_object* v_a_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6133_; 
v_a_6113_ = lean_ctor_get(v___x_6112_, 0);
v_isSharedCheck_6133_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6133_ == 0)
{
v___x_6115_ = v___x_6112_;
v_isShared_6116_ = v_isSharedCheck_6133_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_a_6113_);
lean_dec(v___x_6112_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6133_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6117_; lean_object* v___x_6119_; 
v___x_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6117_, 0, v_a_6113_);
if (v_isShared_6110_ == 0)
{
lean_ctor_set(v___x_6109_, 1, v___x_5979_);
lean_ctor_set(v___x_6109_, 0, v_fst_5952_);
v___x_6119_ = v___x_6109_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_6132_, 1, v___x_5979_);
v___x_6119_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
lean_object* v___x_6121_; 
if (v_isShared_6105_ == 0)
{
lean_ctor_set(v___x_6104_, 1, v___x_6119_);
lean_ctor_set(v___x_6104_, 0, v_fst_5948_);
v___x_6121_ = v___x_6104_;
goto v_reusejp_6120_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v_fst_5948_);
lean_ctor_set(v_reuseFailAlloc_6131_, 1, v___x_6119_);
v___x_6121_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6120_;
}
v_reusejp_6120_:
{
lean_object* v___x_6123_; 
if (v_isShared_6101_ == 0)
{
lean_ctor_set(v___x_6100_, 1, v___x_6121_);
lean_ctor_set(v___x_6100_, 0, v_fst_5944_);
v___x_6123_ = v___x_6100_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_6130_, 1, v___x_6121_);
v___x_6123_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6122_;
}
v_reusejp_6122_:
{
lean_object* v___x_6125_; 
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_6123_);
lean_ctor_set(v___x_5954_, 0, v___x_6117_);
v___x_6125_ = v___x_5954_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6117_);
lean_ctor_set(v_reuseFailAlloc_6129_, 1, v___x_6123_);
v___x_6125_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
lean_object* v___x_6127_; 
if (v_isShared_6116_ == 0)
{
lean_ctor_set(v___x_6115_, 0, v___x_6125_);
v___x_6127_ = v___x_6115_;
goto v_reusejp_6126_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v___x_6125_);
v___x_6127_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6126_;
}
v_reusejp_6126_:
{
return v___x_6127_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6134_; lean_object* v___x_6136_; uint8_t v_isShared_6137_; uint8_t v_isSharedCheck_6141_; 
lean_del_object(v___x_6109_);
lean_del_object(v___x_6104_);
lean_del_object(v___x_6100_);
lean_dec_ref_known(v_fst_5952_, 1);
lean_dec_ref(v___x_5979_);
lean_del_object(v___x_5954_);
lean_dec(v_fst_5948_);
lean_dec(v_fst_5944_);
v_a_6134_ = lean_ctor_get(v___x_6112_, 0);
v_isSharedCheck_6141_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6141_ == 0)
{
v___x_6136_ = v___x_6112_;
v_isShared_6137_ = v_isSharedCheck_6141_;
goto v_resetjp_6135_;
}
else
{
lean_inc(v_a_6134_);
lean_dec(v___x_6112_);
v___x_6136_ = lean_box(0);
v_isShared_6137_ = v_isSharedCheck_6141_;
goto v_resetjp_6135_;
}
v_resetjp_6135_:
{
lean_object* v___x_6139_; 
if (v_isShared_6137_ == 0)
{
v___x_6139_ = v___x_6136_;
goto v_reusejp_6138_;
}
else
{
lean_object* v_reuseFailAlloc_6140_; 
v_reuseFailAlloc_6140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_a_6134_);
v___x_6139_ = v_reuseFailAlloc_6140_;
goto v_reusejp_6138_;
}
v_reusejp_6138_:
{
return v___x_6139_;
}
}
}
}
else
{
lean_object* v_a_6142_; lean_object* v___x_6144_; uint8_t v_isShared_6145_; uint8_t v_isSharedCheck_6149_; 
lean_del_object(v___x_6109_);
lean_dec(v_snd_6107_);
lean_dec(v_fst_6106_);
lean_del_object(v___x_6104_);
lean_dec(v_fst_6102_);
lean_del_object(v___x_6100_);
lean_dec_ref_known(v_fst_5952_, 1);
lean_dec_ref(v___x_5979_);
lean_del_object(v___x_5954_);
lean_dec(v_fst_5948_);
lean_dec(v_fst_5944_);
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
v_a_6142_ = lean_ctor_get(v___x_6111_, 0);
v_isSharedCheck_6149_ = !lean_is_exclusive(v___x_6111_);
if (v_isSharedCheck_6149_ == 0)
{
v___x_6144_ = v___x_6111_;
v_isShared_6145_ = v_isSharedCheck_6149_;
goto v_resetjp_6143_;
}
else
{
lean_inc(v_a_6142_);
lean_dec(v___x_6111_);
v___x_6144_ = lean_box(0);
v_isShared_6145_ = v_isSharedCheck_6149_;
goto v_resetjp_6143_;
}
v_resetjp_6143_:
{
lean_object* v___x_6147_; 
if (v_isShared_6145_ == 0)
{
v___x_6147_ = v___x_6144_;
goto v_reusejp_6146_;
}
else
{
lean_object* v_reuseFailAlloc_6148_; 
v_reuseFailAlloc_6148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_a_6142_);
v___x_6147_ = v_reuseFailAlloc_6148_;
goto v_reusejp_6146_;
}
v_reusejp_6146_:
{
return v___x_6147_;
}
}
}
}
}
}
}
else
{
if (v_stopAtFirstFailure_5920_ == 0)
{
lean_object* v_gs_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6159_; 
lean_del_object(v___x_5983_);
v_gs_6155_ = lean_ctor_get(v_a_5981_, 0);
lean_inc(v_gs_6155_);
lean_dec_ref_known(v_a_5981_, 1);
v___x_6156_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5921_, v_gs_6155_);
v___x_6157_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_5948_, v___x_6156_);
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5979_);
v___x_6159_ = v___x_5954_;
goto v_reusejp_6158_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_6170_, 1, v___x_5979_);
v___x_6159_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6158_;
}
v_reusejp_6158_:
{
lean_object* v___x_6161_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 1, v___x_6159_);
lean_ctor_set(v___x_5950_, 0, v___x_6157_);
v___x_6161_ = v___x_5950_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6157_);
lean_ctor_set(v_reuseFailAlloc_6169_, 1, v___x_6159_);
v___x_6161_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
lean_object* v___x_6163_; 
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v___x_6161_);
v___x_6163_ = v___x_5946_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6168_; 
v_reuseFailAlloc_6168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6168_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_6168_, 1, v___x_6161_);
v___x_6163_ = v_reuseFailAlloc_6168_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
lean_object* v___x_6165_; 
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 1, v___x_6163_);
lean_ctor_set(v___x_5937_, 0, v___x_5959_);
v___x_6165_ = v___x_5937_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v___x_5959_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v___x_6163_);
v___x_6165_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
v_as_x27_5922_ = v_tail_5943_;
v_b_5923_ = v___x_6165_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_gs_6171_; lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6195_; 
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v_gs_6171_ = lean_ctor_get(v_a_5981_, 0);
v_isSharedCheck_6195_ = !lean_is_exclusive(v_a_5981_);
if (v_isSharedCheck_6195_ == 0)
{
v___x_6173_ = v_a_5981_;
v_isShared_6174_ = v_isSharedCheck_6195_;
goto v_resetjp_6172_;
}
else
{
lean_inc(v_gs_6171_);
lean_dec(v_a_5981_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6195_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___x_6175_; lean_object* v___x_6177_; 
v___x_6175_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5921_, v_gs_6171_);
if (v_isShared_6174_ == 0)
{
lean_ctor_set(v___x_6173_, 0, v___x_6175_);
v___x_6177_ = v___x_6173_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v___x_6175_);
v___x_6177_ = v_reuseFailAlloc_6194_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
lean_object* v___x_6178_; lean_object* v___x_6180_; 
v___x_6178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6177_);
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5979_);
v___x_6180_ = v___x_5954_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_6193_, 1, v___x_5979_);
v___x_6180_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
lean_object* v___x_6182_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 1, v___x_6180_);
v___x_6182_ = v___x_5950_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_fst_5948_);
lean_ctor_set(v_reuseFailAlloc_6192_, 1, v___x_6180_);
v___x_6182_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
lean_object* v___x_6184_; 
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v___x_6182_);
v___x_6184_ = v___x_5946_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6191_; 
v_reuseFailAlloc_6191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6191_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_6191_, 1, v___x_6182_);
v___x_6184_ = v_reuseFailAlloc_6191_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
lean_object* v___x_6186_; 
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 1, v___x_6184_);
lean_ctor_set(v___x_5937_, 0, v___x_6178_);
v___x_6186_ = v___x_5937_;
goto v_reusejp_6185_;
}
else
{
lean_object* v_reuseFailAlloc_6190_; 
v_reuseFailAlloc_6190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6190_, 0, v___x_6178_);
lean_ctor_set(v_reuseFailAlloc_6190_, 1, v___x_6184_);
v___x_6186_ = v_reuseFailAlloc_6190_;
goto v_reusejp_6185_;
}
v_reusejp_6185_:
{
lean_object* v___x_6188_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 0, v___x_6186_);
v___x_6188_ = v___x_5983_;
goto v_reusejp_6187_;
}
else
{
lean_object* v_reuseFailAlloc_6189_; 
v_reuseFailAlloc_6189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6189_, 0, v___x_6186_);
v___x_6188_ = v_reuseFailAlloc_6189_;
goto v_reusejp_6187_;
}
v_reusejp_6187_:
{
return v___x_6188_;
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
lean_object* v_a_6197_; lean_object* v___x_6199_; uint8_t v_isShared_6200_; uint8_t v_isSharedCheck_6204_; 
lean_dec_ref(v___x_5979_);
lean_dec(v_start_5956_);
lean_del_object(v___x_5954_);
lean_dec(v_fst_5952_);
lean_del_object(v___x_5950_);
lean_dec(v_fst_5948_);
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5937_);
lean_dec(v___x_5919_);
lean_dec_ref(v_snd_5918_);
lean_dec_ref(v_goal_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_kp_5914_);
v_a_6197_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_6204_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_6204_ == 0)
{
v___x_6199_ = v___x_5980_;
v_isShared_6200_ = v_isSharedCheck_6204_;
goto v_resetjp_6198_;
}
else
{
lean_inc(v_a_6197_);
lean_dec(v___x_5980_);
v___x_6199_ = lean_box(0);
v_isShared_6200_ = v_isSharedCheck_6204_;
goto v_resetjp_6198_;
}
v_resetjp_6198_:
{
lean_object* v___x_6202_; 
if (v_isShared_6200_ == 0)
{
v___x_6202_ = v___x_6199_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6203_; 
v_reuseFailAlloc_6203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6203_, 0, v_a_6197_);
v___x_6202_ = v_reuseFailAlloc_6203_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
return v___x_6202_;
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
lean_object* v_kp_6218_ = _args[0];
lean_object* v_a_6219_ = _args[1];
lean_object* v_goal_6220_ = _args[2];
lean_object* v___x_6221_ = _args[3];
lean_object* v_snd_6222_ = _args[4];
lean_object* v___x_6223_ = _args[5];
lean_object* v_stopAtFirstFailure_6224_ = _args[6];
lean_object* v___x_6225_ = _args[7];
lean_object* v_as_x27_6226_ = _args[8];
lean_object* v_b_6227_ = _args[9];
lean_object* v___y_6228_ = _args[10];
lean_object* v___y_6229_ = _args[11];
lean_object* v___y_6230_ = _args[12];
lean_object* v___y_6231_ = _args[13];
lean_object* v___y_6232_ = _args[14];
lean_object* v___y_6233_ = _args[15];
lean_object* v___y_6234_ = _args[16];
lean_object* v___y_6235_ = _args[17];
lean_object* v___y_6236_ = _args[18];
lean_object* v___y_6237_ = _args[19];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6238_; lean_object* v_res_6239_; 
v_stopAtFirstFailure_boxed_6238_ = lean_unbox(v_stopAtFirstFailure_6224_);
v_res_6239_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6218_, v_a_6219_, v_goal_6220_, v___x_6221_, v_snd_6222_, v___x_6223_, v_stopAtFirstFailure_boxed_6238_, v___x_6225_, v_as_x27_6226_, v_b_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec(v_as_x27_6226_);
lean_dec_ref(v___x_6225_);
lean_dec(v___x_6221_);
return v_res_6239_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v___x_6240_, lean_object* v_c_6241_, lean_object* v___x_6242_, lean_object* v___x_6243_, lean_object* v___x_6244_, uint64_t v_a_6245_, lean_object* v_a_6246_, lean_object* v_a_6247_){
_start:
{
if (lean_obj_tag(v_a_6246_) == 0)
{
lean_object* v___x_6248_; 
lean_dec_ref(v___x_6244_);
lean_dec(v___x_6243_);
lean_dec_ref(v___x_6242_);
lean_dec_ref(v___x_6240_);
v___x_6248_ = lean_array_to_list(v_a_6247_);
return v___x_6248_;
}
else
{
lean_object* v_split_6249_; lean_object* v_head_6250_; lean_object* v_tail_6251_; lean_object* v___x_6253_; uint8_t v_isShared_6254_; uint8_t v_isSharedCheck_6302_; 
v_split_6249_ = lean_ctor_get(v___x_6240_, 15);
lean_inc_ref(v_split_6249_);
v_head_6250_ = lean_ctor_get(v_a_6246_, 0);
v_tail_6251_ = lean_ctor_get(v_a_6246_, 1);
v_isSharedCheck_6302_ = !lean_is_exclusive(v_a_6246_);
if (v_isSharedCheck_6302_ == 0)
{
v___x_6253_ = v_a_6246_;
v_isShared_6254_ = v_isSharedCheck_6302_;
goto v_resetjp_6252_;
}
else
{
lean_inc(v_tail_6251_);
lean_inc(v_head_6250_);
lean_dec(v_a_6246_);
v___x_6253_ = lean_box(0);
v_isShared_6254_ = v_isSharedCheck_6302_;
goto v_resetjp_6252_;
}
v_resetjp_6252_:
{
lean_object* v_nextDeclIdx_6255_; lean_object* v_enodeMap_6256_; lean_object* v_exprs_6257_; lean_object* v_parents_6258_; lean_object* v_congrTable_6259_; lean_object* v_appMap_6260_; lean_object* v_indicesFound_6261_; lean_object* v_toProcess_6262_; lean_object* v_internalizing_6263_; uint8_t v_inconsistent_6264_; lean_object* v_nextIdx_6265_; lean_object* v_newRawFacts_6266_; lean_object* v_facts_6267_; lean_object* v_extThms_6268_; lean_object* v_ematch_6269_; lean_object* v_inj_6270_; lean_object* v_clean_6271_; lean_object* v_sstates_6272_; uint64_t v_introBase_6273_; lean_object* v_numIntros_6274_; lean_object* v_candidates_6275_; lean_object* v_added_6276_; lean_object* v_resolved_6277_; lean_object* v_trace_6278_; lean_object* v_lookaheads_6279_; lean_object* v_argPosMap_6280_; lean_object* v_argsAt_6281_; lean_object* v___x_6283_; uint8_t v_isShared_6284_; uint8_t v_isSharedCheck_6301_; 
v_nextDeclIdx_6255_ = lean_ctor_get(v___x_6240_, 0);
v_enodeMap_6256_ = lean_ctor_get(v___x_6240_, 1);
v_exprs_6257_ = lean_ctor_get(v___x_6240_, 2);
v_parents_6258_ = lean_ctor_get(v___x_6240_, 3);
v_congrTable_6259_ = lean_ctor_get(v___x_6240_, 4);
v_appMap_6260_ = lean_ctor_get(v___x_6240_, 5);
v_indicesFound_6261_ = lean_ctor_get(v___x_6240_, 6);
v_toProcess_6262_ = lean_ctor_get(v___x_6240_, 7);
v_internalizing_6263_ = lean_ctor_get(v___x_6240_, 8);
v_inconsistent_6264_ = lean_ctor_get_uint8(v___x_6240_, sizeof(void*)*20 + 8);
v_nextIdx_6265_ = lean_ctor_get(v___x_6240_, 9);
v_newRawFacts_6266_ = lean_ctor_get(v___x_6240_, 10);
v_facts_6267_ = lean_ctor_get(v___x_6240_, 11);
v_extThms_6268_ = lean_ctor_get(v___x_6240_, 12);
v_ematch_6269_ = lean_ctor_get(v___x_6240_, 13);
v_inj_6270_ = lean_ctor_get(v___x_6240_, 14);
v_clean_6271_ = lean_ctor_get(v___x_6240_, 16);
v_sstates_6272_ = lean_ctor_get(v___x_6240_, 17);
v_introBase_6273_ = lean_ctor_get_uint64(v___x_6240_, sizeof(void*)*20);
v_numIntros_6274_ = lean_ctor_get(v___x_6240_, 19);
v_candidates_6275_ = lean_ctor_get(v_split_6249_, 0);
v_added_6276_ = lean_ctor_get(v_split_6249_, 1);
v_resolved_6277_ = lean_ctor_get(v_split_6249_, 2);
v_trace_6278_ = lean_ctor_get(v_split_6249_, 3);
v_lookaheads_6279_ = lean_ctor_get(v_split_6249_, 4);
v_argPosMap_6280_ = lean_ctor_get(v_split_6249_, 5);
v_argsAt_6281_ = lean_ctor_get(v_split_6249_, 6);
v_isSharedCheck_6301_ = !lean_is_exclusive(v_split_6249_);
if (v_isSharedCheck_6301_ == 0)
{
v___x_6283_ = v_split_6249_;
v_isShared_6284_ = v_isSharedCheck_6301_;
goto v_resetjp_6282_;
}
else
{
lean_inc(v_argsAt_6281_);
lean_inc(v_argPosMap_6280_);
lean_inc(v_lookaheads_6279_);
lean_inc(v_trace_6278_);
lean_inc(v_resolved_6277_);
lean_inc(v_added_6276_);
lean_inc(v_candidates_6275_);
lean_dec(v_split_6249_);
v___x_6283_ = lean_box(0);
v_isShared_6284_ = v_isSharedCheck_6301_;
goto v_resetjp_6282_;
}
v_resetjp_6282_:
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6289_; 
v___x_6285_ = lean_array_get_size(v_a_6247_);
v___x_6286_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_6241_);
lean_inc(v___x_6243_);
lean_inc_ref(v___x_6242_);
v___x_6287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6287_, 0, v___x_6242_);
lean_ctor_set(v___x_6287_, 1, v___x_6285_);
lean_ctor_set(v___x_6287_, 2, v___x_6243_);
lean_ctor_set(v___x_6287_, 3, v___x_6286_);
if (v_isShared_6254_ == 0)
{
lean_ctor_set(v___x_6253_, 1, v_trace_6278_);
lean_ctor_set(v___x_6253_, 0, v___x_6287_);
v___x_6289_ = v___x_6253_;
goto v_reusejp_6288_;
}
else
{
lean_object* v_reuseFailAlloc_6300_; 
v_reuseFailAlloc_6300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6300_, 0, v___x_6287_);
lean_ctor_set(v_reuseFailAlloc_6300_, 1, v_trace_6278_);
v___x_6289_ = v_reuseFailAlloc_6300_;
goto v_reusejp_6288_;
}
v_reusejp_6288_:
{
lean_object* v___x_6291_; 
if (v_isShared_6284_ == 0)
{
lean_ctor_set(v___x_6283_, 3, v___x_6289_);
v___x_6291_ = v___x_6283_;
goto v_reusejp_6290_;
}
else
{
lean_object* v_reuseFailAlloc_6299_; 
v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_candidates_6275_);
lean_ctor_set(v_reuseFailAlloc_6299_, 1, v_added_6276_);
lean_ctor_set(v_reuseFailAlloc_6299_, 2, v_resolved_6277_);
lean_ctor_set(v_reuseFailAlloc_6299_, 3, v___x_6289_);
lean_ctor_set(v_reuseFailAlloc_6299_, 4, v_lookaheads_6279_);
lean_ctor_set(v_reuseFailAlloc_6299_, 5, v_argPosMap_6280_);
lean_ctor_set(v_reuseFailAlloc_6299_, 6, v_argsAt_6281_);
v___x_6291_ = v_reuseFailAlloc_6299_;
goto v_reusejp_6290_;
}
v_reusejp_6290_:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; uint64_t v___x_6294_; uint64_t v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; 
lean_inc(v_numIntros_6274_);
lean_inc_ref(v___x_6244_);
lean_inc_ref(v_sstates_6272_);
lean_inc_ref(v_clean_6271_);
lean_inc_ref(v_inj_6270_);
lean_inc_ref(v_ematch_6269_);
lean_inc_ref(v_extThms_6268_);
lean_inc_ref(v_facts_6267_);
lean_inc_ref(v_newRawFacts_6266_);
lean_inc(v_nextIdx_6265_);
lean_inc_ref(v_internalizing_6263_);
lean_inc_ref(v_toProcess_6262_);
lean_inc_ref(v_indicesFound_6261_);
lean_inc_ref(v_appMap_6260_);
lean_inc_ref(v_congrTable_6259_);
lean_inc_ref(v_parents_6258_);
lean_inc_ref(v_exprs_6257_);
lean_inc_ref(v_enodeMap_6256_);
lean_inc(v_nextDeclIdx_6255_);
v___x_6292_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v___x_6292_, 0, v_nextDeclIdx_6255_);
lean_ctor_set(v___x_6292_, 1, v_enodeMap_6256_);
lean_ctor_set(v___x_6292_, 2, v_exprs_6257_);
lean_ctor_set(v___x_6292_, 3, v_parents_6258_);
lean_ctor_set(v___x_6292_, 4, v_congrTable_6259_);
lean_ctor_set(v___x_6292_, 5, v_appMap_6260_);
lean_ctor_set(v___x_6292_, 6, v_indicesFound_6261_);
lean_ctor_set(v___x_6292_, 7, v_toProcess_6262_);
lean_ctor_set(v___x_6292_, 8, v_internalizing_6263_);
lean_ctor_set(v___x_6292_, 9, v_nextIdx_6265_);
lean_ctor_set(v___x_6292_, 10, v_newRawFacts_6266_);
lean_ctor_set(v___x_6292_, 11, v_facts_6267_);
lean_ctor_set(v___x_6292_, 12, v_extThms_6268_);
lean_ctor_set(v___x_6292_, 13, v_ematch_6269_);
lean_ctor_set(v___x_6292_, 14, v_inj_6270_);
lean_ctor_set(v___x_6292_, 15, v___x_6291_);
lean_ctor_set(v___x_6292_, 16, v_clean_6271_);
lean_ctor_set(v___x_6292_, 17, v_sstates_6272_);
lean_ctor_set(v___x_6292_, 18, v___x_6244_);
lean_ctor_set(v___x_6292_, 19, v_numIntros_6274_);
lean_ctor_set_uint8(v___x_6292_, sizeof(void*)*20 + 8, v_inconsistent_6264_);
lean_ctor_set_uint64(v___x_6292_, sizeof(void*)*20, v_introBase_6273_);
v___x_6293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6293_, 0, v___x_6292_);
lean_ctor_set(v___x_6293_, 1, v_head_6250_);
v___x_6294_ = lean_uint64_of_nat(v___x_6285_);
v___x_6295_ = lean_uint64_mix_hash(v_a_6245_, v___x_6294_);
v___x_6296_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_6293_, v___x_6295_);
v___x_6297_ = lean_array_push(v_a_6247_, v___x_6296_);
v_a_6246_ = v_tail_6251_;
v_a_6247_ = v___x_6297_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v___x_6303_, lean_object* v_c_6304_, lean_object* v___x_6305_, lean_object* v___x_6306_, lean_object* v___x_6307_, lean_object* v_a_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_){
_start:
{
uint64_t v_a_118062__boxed_6311_; lean_object* v_res_6312_; 
v_a_118062__boxed_6311_ = lean_unbox_uint64(v_a_6308_);
lean_dec_ref(v_a_6308_);
v_res_6312_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_6303_, v_c_6304_, v___x_6305_, v___x_6306_, v___x_6307_, v_a_118062__boxed_6311_, v_a_6309_, v_a_6310_);
lean_dec_ref(v_c_6304_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_6313_, lean_object* v_x_6314_, lean_object* v_x_6315_, lean_object* v_x_6316_){
_start:
{
lean_object* v_ks_6317_; lean_object* v_vs_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6342_; 
v_ks_6317_ = lean_ctor_get(v_x_6313_, 0);
v_vs_6318_ = lean_ctor_get(v_x_6313_, 1);
v_isSharedCheck_6342_ = !lean_is_exclusive(v_x_6313_);
if (v_isSharedCheck_6342_ == 0)
{
v___x_6320_ = v_x_6313_;
v_isShared_6321_ = v_isSharedCheck_6342_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_vs_6318_);
lean_inc(v_ks_6317_);
lean_dec(v_x_6313_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6342_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
lean_object* v___x_6322_; uint8_t v___x_6323_; 
v___x_6322_ = lean_array_get_size(v_ks_6317_);
v___x_6323_ = lean_nat_dec_lt(v_x_6314_, v___x_6322_);
if (v___x_6323_ == 0)
{
lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6327_; 
lean_dec(v_x_6314_);
v___x_6324_ = lean_array_push(v_ks_6317_, v_x_6315_);
v___x_6325_ = lean_array_push(v_vs_6318_, v_x_6316_);
if (v_isShared_6321_ == 0)
{
lean_ctor_set(v___x_6320_, 1, v___x_6325_);
lean_ctor_set(v___x_6320_, 0, v___x_6324_);
v___x_6327_ = v___x_6320_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6328_; 
v_reuseFailAlloc_6328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6328_, 0, v___x_6324_);
lean_ctor_set(v_reuseFailAlloc_6328_, 1, v___x_6325_);
v___x_6327_ = v_reuseFailAlloc_6328_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
return v___x_6327_;
}
}
else
{
lean_object* v_k_x27_6329_; uint8_t v___x_6330_; 
v_k_x27_6329_ = lean_array_fget_borrowed(v_ks_6317_, v_x_6314_);
v___x_6330_ = l_Lean_instBEqMVarId_beq(v_x_6315_, v_k_x27_6329_);
if (v___x_6330_ == 0)
{
lean_object* v___x_6332_; 
if (v_isShared_6321_ == 0)
{
v___x_6332_ = v___x_6320_;
goto v_reusejp_6331_;
}
else
{
lean_object* v_reuseFailAlloc_6336_; 
v_reuseFailAlloc_6336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_ks_6317_);
lean_ctor_set(v_reuseFailAlloc_6336_, 1, v_vs_6318_);
v___x_6332_ = v_reuseFailAlloc_6336_;
goto v_reusejp_6331_;
}
v_reusejp_6331_:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; 
v___x_6333_ = lean_unsigned_to_nat(1u);
v___x_6334_ = lean_nat_add(v_x_6314_, v___x_6333_);
lean_dec(v_x_6314_);
v_x_6313_ = v___x_6332_;
v_x_6314_ = v___x_6334_;
goto _start;
}
}
else
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6340_; 
v___x_6337_ = lean_array_fset(v_ks_6317_, v_x_6314_, v_x_6315_);
v___x_6338_ = lean_array_fset(v_vs_6318_, v_x_6314_, v_x_6316_);
lean_dec(v_x_6314_);
if (v_isShared_6321_ == 0)
{
lean_ctor_set(v___x_6320_, 1, v___x_6338_);
lean_ctor_set(v___x_6320_, 0, v___x_6337_);
v___x_6340_ = v___x_6320_;
goto v_reusejp_6339_;
}
else
{
lean_object* v_reuseFailAlloc_6341_; 
v_reuseFailAlloc_6341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6341_, 0, v___x_6337_);
lean_ctor_set(v_reuseFailAlloc_6341_, 1, v___x_6338_);
v___x_6340_ = v_reuseFailAlloc_6341_;
goto v_reusejp_6339_;
}
v_reusejp_6339_:
{
return v___x_6340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(lean_object* v_n_6343_, lean_object* v_k_6344_, lean_object* v_v_6345_){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6346_ = lean_unsigned_to_nat(0u);
v___x_6347_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_n_6343_, v___x_6346_, v_k_6344_, v_v_6345_);
return v___x_6347_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_6348_; 
v___x_6348_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_6348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(lean_object* v_x_6349_, size_t v_x_6350_, size_t v_x_6351_, lean_object* v_x_6352_, lean_object* v_x_6353_){
_start:
{
if (lean_obj_tag(v_x_6349_) == 0)
{
lean_object* v_es_6354_; size_t v___x_6355_; size_t v___x_6356_; lean_object* v_j_6357_; lean_object* v___x_6358_; uint8_t v___x_6359_; 
v_es_6354_ = lean_ctor_get(v_x_6349_, 0);
v___x_6355_ = ((size_t)31ULL);
v___x_6356_ = lean_usize_land(v_x_6350_, v___x_6355_);
v_j_6357_ = lean_usize_to_nat(v___x_6356_);
v___x_6358_ = lean_array_get_size(v_es_6354_);
v___x_6359_ = lean_nat_dec_lt(v_j_6357_, v___x_6358_);
if (v___x_6359_ == 0)
{
lean_dec(v_j_6357_);
lean_dec(v_x_6353_);
lean_dec(v_x_6352_);
return v_x_6349_;
}
else
{
lean_object* v___x_6361_; uint8_t v_isShared_6362_; uint8_t v_isSharedCheck_6398_; 
lean_inc_ref(v_es_6354_);
v_isSharedCheck_6398_ = !lean_is_exclusive(v_x_6349_);
if (v_isSharedCheck_6398_ == 0)
{
lean_object* v_unused_6399_; 
v_unused_6399_ = lean_ctor_get(v_x_6349_, 0);
lean_dec(v_unused_6399_);
v___x_6361_ = v_x_6349_;
v_isShared_6362_ = v_isSharedCheck_6398_;
goto v_resetjp_6360_;
}
else
{
lean_dec(v_x_6349_);
v___x_6361_ = lean_box(0);
v_isShared_6362_ = v_isSharedCheck_6398_;
goto v_resetjp_6360_;
}
v_resetjp_6360_:
{
lean_object* v_v_6363_; lean_object* v___x_6364_; lean_object* v_xs_x27_6365_; lean_object* v___y_6367_; 
v_v_6363_ = lean_array_fget(v_es_6354_, v_j_6357_);
v___x_6364_ = lean_box(0);
v_xs_x27_6365_ = lean_array_fset(v_es_6354_, v_j_6357_, v___x_6364_);
switch(lean_obj_tag(v_v_6363_))
{
case 0:
{
lean_object* v_key_6372_; lean_object* v_val_6373_; lean_object* v___x_6375_; uint8_t v_isShared_6376_; uint8_t v_isSharedCheck_6383_; 
v_key_6372_ = lean_ctor_get(v_v_6363_, 0);
v_val_6373_ = lean_ctor_get(v_v_6363_, 1);
v_isSharedCheck_6383_ = !lean_is_exclusive(v_v_6363_);
if (v_isSharedCheck_6383_ == 0)
{
v___x_6375_ = v_v_6363_;
v_isShared_6376_ = v_isSharedCheck_6383_;
goto v_resetjp_6374_;
}
else
{
lean_inc(v_val_6373_);
lean_inc(v_key_6372_);
lean_dec(v_v_6363_);
v___x_6375_ = lean_box(0);
v_isShared_6376_ = v_isSharedCheck_6383_;
goto v_resetjp_6374_;
}
v_resetjp_6374_:
{
uint8_t v___x_6377_; 
v___x_6377_ = l_Lean_instBEqMVarId_beq(v_x_6352_, v_key_6372_);
if (v___x_6377_ == 0)
{
lean_object* v___x_6378_; lean_object* v___x_6379_; 
lean_del_object(v___x_6375_);
v___x_6378_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_6372_, v_val_6373_, v_x_6352_, v_x_6353_);
v___x_6379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6379_, 0, v___x_6378_);
v___y_6367_ = v___x_6379_;
goto v___jp_6366_;
}
else
{
lean_object* v___x_6381_; 
lean_dec(v_val_6373_);
lean_dec(v_key_6372_);
if (v_isShared_6376_ == 0)
{
lean_ctor_set(v___x_6375_, 1, v_x_6353_);
lean_ctor_set(v___x_6375_, 0, v_x_6352_);
v___x_6381_ = v___x_6375_;
goto v_reusejp_6380_;
}
else
{
lean_object* v_reuseFailAlloc_6382_; 
v_reuseFailAlloc_6382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_x_6352_);
lean_ctor_set(v_reuseFailAlloc_6382_, 1, v_x_6353_);
v___x_6381_ = v_reuseFailAlloc_6382_;
goto v_reusejp_6380_;
}
v_reusejp_6380_:
{
v___y_6367_ = v___x_6381_;
goto v___jp_6366_;
}
}
}
}
case 1:
{
lean_object* v_node_6384_; lean_object* v___x_6386_; uint8_t v_isShared_6387_; uint8_t v_isSharedCheck_6396_; 
v_node_6384_ = lean_ctor_get(v_v_6363_, 0);
v_isSharedCheck_6396_ = !lean_is_exclusive(v_v_6363_);
if (v_isSharedCheck_6396_ == 0)
{
v___x_6386_ = v_v_6363_;
v_isShared_6387_ = v_isSharedCheck_6396_;
goto v_resetjp_6385_;
}
else
{
lean_inc(v_node_6384_);
lean_dec(v_v_6363_);
v___x_6386_ = lean_box(0);
v_isShared_6387_ = v_isSharedCheck_6396_;
goto v_resetjp_6385_;
}
v_resetjp_6385_:
{
size_t v___x_6388_; size_t v___x_6389_; size_t v___x_6390_; size_t v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6394_; 
v___x_6388_ = ((size_t)5ULL);
v___x_6389_ = lean_usize_shift_right(v_x_6350_, v___x_6388_);
v___x_6390_ = ((size_t)1ULL);
v___x_6391_ = lean_usize_add(v_x_6351_, v___x_6390_);
v___x_6392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_node_6384_, v___x_6389_, v___x_6391_, v_x_6352_, v_x_6353_);
if (v_isShared_6387_ == 0)
{
lean_ctor_set(v___x_6386_, 0, v___x_6392_);
v___x_6394_ = v___x_6386_;
goto v_reusejp_6393_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v___x_6392_);
v___x_6394_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6393_;
}
v_reusejp_6393_:
{
v___y_6367_ = v___x_6394_;
goto v___jp_6366_;
}
}
}
default: 
{
lean_object* v___x_6397_; 
v___x_6397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6397_, 0, v_x_6352_);
lean_ctor_set(v___x_6397_, 1, v_x_6353_);
v___y_6367_ = v___x_6397_;
goto v___jp_6366_;
}
}
v___jp_6366_:
{
lean_object* v___x_6368_; lean_object* v___x_6370_; 
v___x_6368_ = lean_array_fset(v_xs_x27_6365_, v_j_6357_, v___y_6367_);
lean_dec(v_j_6357_);
if (v_isShared_6362_ == 0)
{
lean_ctor_set(v___x_6361_, 0, v___x_6368_);
v___x_6370_ = v___x_6361_;
goto v_reusejp_6369_;
}
else
{
lean_object* v_reuseFailAlloc_6371_; 
v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6371_, 0, v___x_6368_);
v___x_6370_ = v_reuseFailAlloc_6371_;
goto v_reusejp_6369_;
}
v_reusejp_6369_:
{
return v___x_6370_;
}
}
}
}
}
else
{
lean_object* v_ks_6400_; lean_object* v_vs_6401_; lean_object* v___x_6403_; uint8_t v_isShared_6404_; uint8_t v_isSharedCheck_6419_; 
v_ks_6400_ = lean_ctor_get(v_x_6349_, 0);
v_vs_6401_ = lean_ctor_get(v_x_6349_, 1);
v_isSharedCheck_6419_ = !lean_is_exclusive(v_x_6349_);
if (v_isSharedCheck_6419_ == 0)
{
v___x_6403_ = v_x_6349_;
v_isShared_6404_ = v_isSharedCheck_6419_;
goto v_resetjp_6402_;
}
else
{
lean_inc(v_vs_6401_);
lean_inc(v_ks_6400_);
lean_dec(v_x_6349_);
v___x_6403_ = lean_box(0);
v_isShared_6404_ = v_isSharedCheck_6419_;
goto v_resetjp_6402_;
}
v_resetjp_6402_:
{
lean_object* v___x_6406_; 
if (v_isShared_6404_ == 0)
{
v___x_6406_ = v___x_6403_;
goto v_reusejp_6405_;
}
else
{
lean_object* v_reuseFailAlloc_6418_; 
v_reuseFailAlloc_6418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_ks_6400_);
lean_ctor_set(v_reuseFailAlloc_6418_, 1, v_vs_6401_);
v___x_6406_ = v_reuseFailAlloc_6418_;
goto v_reusejp_6405_;
}
v_reusejp_6405_:
{
lean_object* v_newNode_6407_; size_t v___x_6408_; uint8_t v___x_6409_; 
v_newNode_6407_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v___x_6406_, v_x_6352_, v_x_6353_);
v___x_6408_ = ((size_t)7ULL);
v___x_6409_ = lean_usize_dec_le(v___x_6408_, v_x_6351_);
if (v___x_6409_ == 0)
{
lean_object* v___x_6410_; lean_object* v___x_6411_; uint8_t v___x_6412_; 
v___x_6410_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_6407_);
v___x_6411_ = lean_unsigned_to_nat(4u);
v___x_6412_ = lean_nat_dec_lt(v___x_6410_, v___x_6411_);
lean_dec(v___x_6410_);
if (v___x_6412_ == 0)
{
lean_object* v_ks_6413_; lean_object* v_vs_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; 
v_ks_6413_ = lean_ctor_get(v_newNode_6407_, 0);
lean_inc_ref(v_ks_6413_);
v_vs_6414_ = lean_ctor_get(v_newNode_6407_, 1);
lean_inc_ref(v_vs_6414_);
lean_dec_ref(v_newNode_6407_);
v___x_6415_ = lean_unsigned_to_nat(0u);
v___x_6416_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0);
v___x_6417_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_x_6351_, v_ks_6413_, v_vs_6414_, v___x_6415_, v___x_6416_);
lean_dec_ref(v_vs_6414_);
lean_dec_ref(v_ks_6413_);
return v___x_6417_;
}
else
{
return v_newNode_6407_;
}
}
else
{
return v_newNode_6407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(size_t v_depth_6420_, lean_object* v_keys_6421_, lean_object* v_vals_6422_, lean_object* v_i_6423_, lean_object* v_entries_6424_){
_start:
{
lean_object* v___x_6425_; uint8_t v___x_6426_; 
v___x_6425_ = lean_array_get_size(v_keys_6421_);
v___x_6426_ = lean_nat_dec_lt(v_i_6423_, v___x_6425_);
if (v___x_6426_ == 0)
{
lean_dec(v_i_6423_);
return v_entries_6424_;
}
else
{
lean_object* v_k_6427_; lean_object* v_v_6428_; uint64_t v___x_6429_; size_t v_h_6430_; size_t v___x_6431_; lean_object* v___x_6432_; size_t v___x_6433_; size_t v___x_6434_; size_t v___x_6435_; size_t v_h_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
v_k_6427_ = lean_array_fget_borrowed(v_keys_6421_, v_i_6423_);
v_v_6428_ = lean_array_fget_borrowed(v_vals_6422_, v_i_6423_);
v___x_6429_ = l_Lean_instHashableMVarId_hash(v_k_6427_);
v_h_6430_ = lean_uint64_to_usize(v___x_6429_);
v___x_6431_ = ((size_t)5ULL);
v___x_6432_ = lean_unsigned_to_nat(1u);
v___x_6433_ = ((size_t)1ULL);
v___x_6434_ = lean_usize_sub(v_depth_6420_, v___x_6433_);
v___x_6435_ = lean_usize_mul(v___x_6431_, v___x_6434_);
v_h_6436_ = lean_usize_shift_right(v_h_6430_, v___x_6435_);
v___x_6437_ = lean_nat_add(v_i_6423_, v___x_6432_);
lean_dec(v_i_6423_);
lean_inc(v_v_6428_);
lean_inc(v_k_6427_);
v___x_6438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_entries_6424_, v_h_6436_, v_depth_6420_, v_k_6427_, v_v_6428_);
v_i_6423_ = v___x_6437_;
v_entries_6424_ = v___x_6438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_depth_6440_, lean_object* v_keys_6441_, lean_object* v_vals_6442_, lean_object* v_i_6443_, lean_object* v_entries_6444_){
_start:
{
size_t v_depth_boxed_6445_; lean_object* v_res_6446_; 
v_depth_boxed_6445_ = lean_unbox_usize(v_depth_6440_);
lean_dec(v_depth_6440_);
v_res_6446_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_boxed_6445_, v_keys_6441_, v_vals_6442_, v_i_6443_, v_entries_6444_);
lean_dec_ref(v_vals_6442_);
lean_dec_ref(v_keys_6441_);
return v_res_6446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_x_6447_, lean_object* v_x_6448_, lean_object* v_x_6449_, lean_object* v_x_6450_, lean_object* v_x_6451_){
_start:
{
size_t v_x_118210__boxed_6452_; size_t v_x_118211__boxed_6453_; lean_object* v_res_6454_; 
v_x_118210__boxed_6452_ = lean_unbox_usize(v_x_6448_);
lean_dec(v_x_6448_);
v_x_118211__boxed_6453_ = lean_unbox_usize(v_x_6449_);
lean_dec(v_x_6449_);
v_res_6454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6447_, v_x_118210__boxed_6452_, v_x_118211__boxed_6453_, v_x_6450_, v_x_6451_);
return v_res_6454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(lean_object* v_x_6455_, lean_object* v_x_6456_, lean_object* v_x_6457_){
_start:
{
uint64_t v___x_6458_; size_t v___x_6459_; size_t v___x_6460_; lean_object* v___x_6461_; 
v___x_6458_ = l_Lean_instHashableMVarId_hash(v_x_6456_);
v___x_6459_ = lean_uint64_to_usize(v___x_6458_);
v___x_6460_ = ((size_t)1ULL);
v___x_6461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6455_, v___x_6459_, v___x_6460_, v_x_6456_, v_x_6457_);
return v___x_6461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_mvarId_6462_, lean_object* v_val_6463_, lean_object* v___y_6464_){
_start:
{
lean_object* v___x_6466_; lean_object* v_mctx_6467_; lean_object* v_cache_6468_; lean_object* v_zetaDeltaFVarIds_6469_; lean_object* v_postponed_6470_; lean_object* v_diag_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6500_; 
v___x_6466_ = lean_st_ref_take(v___y_6464_);
v_mctx_6467_ = lean_ctor_get(v___x_6466_, 0);
v_cache_6468_ = lean_ctor_get(v___x_6466_, 1);
v_zetaDeltaFVarIds_6469_ = lean_ctor_get(v___x_6466_, 2);
v_postponed_6470_ = lean_ctor_get(v___x_6466_, 3);
v_diag_6471_ = lean_ctor_get(v___x_6466_, 4);
v_isSharedCheck_6500_ = !lean_is_exclusive(v___x_6466_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6473_ = v___x_6466_;
v_isShared_6474_ = v_isSharedCheck_6500_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_diag_6471_);
lean_inc(v_postponed_6470_);
lean_inc(v_zetaDeltaFVarIds_6469_);
lean_inc(v_cache_6468_);
lean_inc(v_mctx_6467_);
lean_dec(v___x_6466_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6500_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v_depth_6475_; lean_object* v_levelAssignDepth_6476_; lean_object* v_lmvarCounter_6477_; lean_object* v_mvarCounter_6478_; lean_object* v_lDecls_6479_; lean_object* v_decls_6480_; lean_object* v_userNames_6481_; lean_object* v_lAssignment_6482_; lean_object* v_eAssignment_6483_; lean_object* v_dAssignment_6484_; lean_object* v_instanceTypedMVars_6485_; lean_object* v___x_6487_; uint8_t v_isShared_6488_; uint8_t v_isSharedCheck_6499_; 
v_depth_6475_ = lean_ctor_get(v_mctx_6467_, 0);
v_levelAssignDepth_6476_ = lean_ctor_get(v_mctx_6467_, 1);
v_lmvarCounter_6477_ = lean_ctor_get(v_mctx_6467_, 2);
v_mvarCounter_6478_ = lean_ctor_get(v_mctx_6467_, 3);
v_lDecls_6479_ = lean_ctor_get(v_mctx_6467_, 4);
v_decls_6480_ = lean_ctor_get(v_mctx_6467_, 5);
v_userNames_6481_ = lean_ctor_get(v_mctx_6467_, 6);
v_lAssignment_6482_ = lean_ctor_get(v_mctx_6467_, 7);
v_eAssignment_6483_ = lean_ctor_get(v_mctx_6467_, 8);
v_dAssignment_6484_ = lean_ctor_get(v_mctx_6467_, 9);
v_instanceTypedMVars_6485_ = lean_ctor_get(v_mctx_6467_, 10);
v_isSharedCheck_6499_ = !lean_is_exclusive(v_mctx_6467_);
if (v_isSharedCheck_6499_ == 0)
{
v___x_6487_ = v_mctx_6467_;
v_isShared_6488_ = v_isSharedCheck_6499_;
goto v_resetjp_6486_;
}
else
{
lean_inc(v_instanceTypedMVars_6485_);
lean_inc(v_dAssignment_6484_);
lean_inc(v_eAssignment_6483_);
lean_inc(v_lAssignment_6482_);
lean_inc(v_userNames_6481_);
lean_inc(v_decls_6480_);
lean_inc(v_lDecls_6479_);
lean_inc(v_mvarCounter_6478_);
lean_inc(v_lmvarCounter_6477_);
lean_inc(v_levelAssignDepth_6476_);
lean_inc(v_depth_6475_);
lean_dec(v_mctx_6467_);
v___x_6487_ = lean_box(0);
v_isShared_6488_ = v_isSharedCheck_6499_;
goto v_resetjp_6486_;
}
v_resetjp_6486_:
{
lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6492_; 
v___x_6489_ = lean_box(0);
v___x_6490_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_eAssignment_6483_, v_mvarId_6462_, v_val_6463_);
if (v_isShared_6488_ == 0)
{
lean_ctor_set(v___x_6487_, 8, v___x_6490_);
v___x_6492_ = v___x_6487_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6498_; 
v_reuseFailAlloc_6498_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_6498_, 0, v_depth_6475_);
lean_ctor_set(v_reuseFailAlloc_6498_, 1, v_levelAssignDepth_6476_);
lean_ctor_set(v_reuseFailAlloc_6498_, 2, v_lmvarCounter_6477_);
lean_ctor_set(v_reuseFailAlloc_6498_, 3, v_mvarCounter_6478_);
lean_ctor_set(v_reuseFailAlloc_6498_, 4, v_lDecls_6479_);
lean_ctor_set(v_reuseFailAlloc_6498_, 5, v_decls_6480_);
lean_ctor_set(v_reuseFailAlloc_6498_, 6, v_userNames_6481_);
lean_ctor_set(v_reuseFailAlloc_6498_, 7, v_lAssignment_6482_);
lean_ctor_set(v_reuseFailAlloc_6498_, 8, v___x_6490_);
lean_ctor_set(v_reuseFailAlloc_6498_, 9, v_dAssignment_6484_);
lean_ctor_set(v_reuseFailAlloc_6498_, 10, v_instanceTypedMVars_6485_);
v___x_6492_ = v_reuseFailAlloc_6498_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
lean_object* v___x_6494_; 
if (v_isShared_6474_ == 0)
{
lean_ctor_set(v___x_6473_, 0, v___x_6492_);
v___x_6494_ = v___x_6473_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v___x_6492_);
lean_ctor_set(v_reuseFailAlloc_6497_, 1, v_cache_6468_);
lean_ctor_set(v_reuseFailAlloc_6497_, 2, v_zetaDeltaFVarIds_6469_);
lean_ctor_set(v_reuseFailAlloc_6497_, 3, v_postponed_6470_);
lean_ctor_set(v_reuseFailAlloc_6497_, 4, v_diag_6471_);
v___x_6494_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; 
v___x_6495_ = lean_st_ref_put(v___y_6464_, v___x_6494_);
v___x_6496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6496_, 0, v___x_6489_);
return v___x_6496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_mvarId_6501_, lean_object* v_val_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_){
_start:
{
lean_object* v_res_6505_; 
v_res_6505_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6501_, v_val_6502_, v___y_6503_);
lean_dec(v___y_6503_);
return v_res_6505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(lean_object* v_goal_6510_, lean_object* v_c_6511_, lean_object* v_numCases_6512_, uint8_t v_isRec_6513_, lean_object* v_candidates_x3f_6514_, uint8_t v_compress_6515_, lean_object* v_kp_6516_, uint8_t v_stopAtFirstFailure_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_){
_start:
{
lean_object* v___x_6528_; 
v___x_6528_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_6519_);
if (lean_obj_tag(v___x_6528_) == 0)
{
lean_object* v_a_6529_; uint8_t v_trace_6530_; lean_object* v___x_6531_; 
v_a_6529_ = lean_ctor_get(v___x_6528_, 0);
lean_inc(v_a_6529_);
lean_dec_ref_known(v___x_6528_, 1);
v_trace_6530_ = lean_ctor_get_uint8(v_a_6529_, sizeof(void*)*18);
lean_dec(v_a_6529_);
v___x_6531_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v___y_6519_, v___y_6520_, v___y_6524_, v___y_6526_);
if (lean_obj_tag(v___x_6531_) == 0)
{
lean_object* v_a_6532_; lean_object* v___x_6533_; 
v_a_6532_ = lean_ctor_get(v___x_6531_, 0);
lean_inc(v_a_6532_);
lean_dec_ref_known(v___x_6531_, 1);
lean_inc_ref(v_goal_6510_);
v___x_6533_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_6510_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
if (lean_obj_tag(v___x_6533_) == 0)
{
lean_object* v_a_6534_; lean_object* v_mvarId_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___f_6538_; lean_object* v___x_6539_; lean_object* v___f_6540_; lean_object* v___x_6541_; 
v_a_6534_ = lean_ctor_get(v___x_6533_, 0);
lean_inc_n(v_a_6534_, 2);
lean_dec_ref_known(v___x_6533_, 1);
v_mvarId_6535_ = lean_ctor_get(v_goal_6510_, 1);
v___x_6536_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6511_);
v___x_6537_ = lean_box(v_isRec_6513_);
lean_inc_ref_n(v_c_6511_, 2);
lean_inc_ref(v___x_6536_);
v___f_6538_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6538_, 0, v___x_6536_);
lean_closure_set(v___f_6538_, 1, v_c_6511_);
lean_closure_set(v___f_6538_, 2, v_a_6534_);
lean_closure_set(v___f_6538_, 3, v_numCases_6512_);
lean_closure_set(v___f_6538_, 4, v___x_6537_);
v___x_6539_ = lean_box(v_trace_6530_);
lean_inc_ref(v_goal_6510_);
v___f_6540_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_6540_, 0, v_goal_6510_);
lean_closure_set(v___f_6540_, 1, v___x_6539_);
lean_closure_set(v___f_6540_, 2, v___f_6538_);
lean_closure_set(v___f_6540_, 3, v_c_6511_);
lean_closure_set(v___f_6540_, 4, v_candidates_x3f_6514_);
lean_inc(v_mvarId_6535_);
v___x_6541_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6535_, v___f_6540_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
if (lean_obj_tag(v___x_6541_) == 0)
{
lean_object* v_a_6542_; lean_object* v___x_6544_; uint8_t v_isShared_6545_; uint8_t v_isSharedCheck_6721_; 
v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6544_ = v___x_6541_;
v_isShared_6545_ = v_isSharedCheck_6721_;
goto v_resetjp_6543_;
}
else
{
lean_inc(v_a_6542_);
lean_dec(v___x_6541_);
v___x_6544_ = lean_box(0);
v_isShared_6545_ = v_isSharedCheck_6721_;
goto v_resetjp_6543_;
}
v_resetjp_6543_:
{
lean_object* v_fst_6546_; lean_object* v_snd_6547_; lean_object* v___x_6549_; uint8_t v_isShared_6550_; uint8_t v_isSharedCheck_6720_; 
v_fst_6546_ = lean_ctor_get(v_a_6542_, 0);
v_snd_6547_ = lean_ctor_get(v_a_6542_, 1);
v_isSharedCheck_6720_ = !lean_is_exclusive(v_a_6542_);
if (v_isSharedCheck_6720_ == 0)
{
v___x_6549_ = v_a_6542_;
v_isShared_6550_ = v_isSharedCheck_6720_;
goto v_resetjp_6548_;
}
else
{
lean_inc(v_snd_6547_);
lean_inc(v_fst_6546_);
lean_dec(v_a_6542_);
v___x_6549_ = lean_box(0);
v_isShared_6550_ = v_isSharedCheck_6720_;
goto v_resetjp_6548_;
}
v_resetjp_6548_:
{
lean_object* v_fst_6551_; lean_object* v_snd_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6719_; 
v_fst_6551_ = lean_ctor_get(v_fst_6546_, 0);
v_snd_6552_ = lean_ctor_get(v_fst_6546_, 1);
v_isSharedCheck_6719_ = !lean_is_exclusive(v_fst_6546_);
if (v_isSharedCheck_6719_ == 0)
{
v___x_6554_ = v_fst_6546_;
v_isShared_6555_ = v_isSharedCheck_6719_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_snd_6552_);
lean_inc(v_fst_6551_);
lean_dec(v_fst_6546_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6719_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6559_; lean_object* v___y_6560_; lean_object* v___y_6561_; lean_object* v___f_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v_congrThms_6611_; lean_object* v_simp_6612_; lean_object* v_symSimp_6613_; lean_object* v_symDSimp_6614_; lean_object* v_lastTag_6615_; lean_object* v_counters_6616_; lean_object* v_splitDiags_6617_; lean_object* v_ematchDiags_6618_; lean_object* v_lawfulEqCmpMap_6619_; lean_object* v_reflCmpMap_6620_; lean_object* v_anchors_6621_; lean_object* v_fvarAnchors_6622_; lean_object* v_instanceMap_6623_; lean_object* v_hoistedDecls_6624_; lean_object* v_proofInfos_6625_; lean_object* v_numBranches_6626_; lean_object* v___x_6628_; uint8_t v_isShared_6629_; uint8_t v_isSharedCheck_6718_; 
lean_inc(v_snd_6547_);
v___f_6608_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed), 12, 2);
lean_closure_set(v___f_6608_, 0, v_snd_6547_);
lean_closure_set(v___f_6608_, 1, v_a_6534_);
v___x_6609_ = l_List_lengthTR___redArg(v_fst_6551_);
v___x_6610_ = lean_st_ref_take(v___y_6520_);
v_congrThms_6611_ = lean_ctor_get(v___x_6610_, 0);
v_simp_6612_ = lean_ctor_get(v___x_6610_, 1);
v_symSimp_6613_ = lean_ctor_get(v___x_6610_, 2);
v_symDSimp_6614_ = lean_ctor_get(v___x_6610_, 3);
v_lastTag_6615_ = lean_ctor_get(v___x_6610_, 4);
v_counters_6616_ = lean_ctor_get(v___x_6610_, 5);
v_splitDiags_6617_ = lean_ctor_get(v___x_6610_, 6);
v_ematchDiags_6618_ = lean_ctor_get(v___x_6610_, 7);
v_lawfulEqCmpMap_6619_ = lean_ctor_get(v___x_6610_, 8);
v_reflCmpMap_6620_ = lean_ctor_get(v___x_6610_, 9);
v_anchors_6621_ = lean_ctor_get(v___x_6610_, 10);
v_fvarAnchors_6622_ = lean_ctor_get(v___x_6610_, 11);
v_instanceMap_6623_ = lean_ctor_get(v___x_6610_, 12);
v_hoistedDecls_6624_ = lean_ctor_get(v___x_6610_, 13);
v_proofInfos_6625_ = lean_ctor_get(v___x_6610_, 14);
v_numBranches_6626_ = lean_ctor_get(v___x_6610_, 15);
v_isSharedCheck_6718_ = !lean_is_exclusive(v___x_6610_);
if (v_isSharedCheck_6718_ == 0)
{
v___x_6628_ = v___x_6610_;
v_isShared_6629_ = v_isSharedCheck_6718_;
goto v_resetjp_6627_;
}
else
{
lean_inc(v_numBranches_6626_);
lean_inc(v_proofInfos_6625_);
lean_inc(v_hoistedDecls_6624_);
lean_inc(v_instanceMap_6623_);
lean_inc(v_fvarAnchors_6622_);
lean_inc(v_anchors_6621_);
lean_inc(v_reflCmpMap_6620_);
lean_inc(v_lawfulEqCmpMap_6619_);
lean_inc(v_ematchDiags_6618_);
lean_inc(v_splitDiags_6617_);
lean_inc(v_counters_6616_);
lean_inc(v_lastTag_6615_);
lean_inc(v_symDSimp_6614_);
lean_inc(v_symSimp_6613_);
lean_inc(v_simp_6612_);
lean_inc(v_congrThms_6611_);
lean_dec(v___x_6610_);
v___x_6628_ = lean_box(0);
v_isShared_6629_ = v_isSharedCheck_6718_;
goto v_resetjp_6627_;
}
v___jp_6556_:
{
lean_object* v___x_6562_; uint8_t v___x_6563_; 
v___x_6562_ = lean_array_get_size(v___y_6559_);
v___x_6563_ = lean_nat_dec_eq(v___x_6562_, v___y_6557_);
if (v___x_6563_ == 0)
{
lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6567_; 
lean_dec(v___y_6558_);
lean_dec(v_snd_6552_);
v___x_6564_ = lean_array_to_list(v___y_6559_);
v___x_6565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6565_, 0, v___x_6564_);
if (v_isShared_6545_ == 0)
{
lean_ctor_set(v___x_6544_, 0, v___x_6565_);
v___x_6567_ = v___x_6544_;
goto v_reusejp_6566_;
}
else
{
lean_object* v_reuseFailAlloc_6568_; 
v_reuseFailAlloc_6568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6568_, 0, v___x_6565_);
v___x_6567_ = v_reuseFailAlloc_6568_;
goto v_reusejp_6566_;
}
v_reusejp_6566_:
{
return v___x_6567_;
}
}
else
{
lean_dec(v___y_6559_);
if (lean_obj_tag(v_snd_6552_) == 1)
{
lean_object* v_val_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6603_; 
lean_del_object(v___x_6544_);
v_val_6569_ = lean_ctor_get(v_snd_6552_, 0);
v_isSharedCheck_6603_ = !lean_is_exclusive(v_snd_6552_);
if (v_isSharedCheck_6603_ == 0)
{
v___x_6571_ = v_snd_6552_;
v_isShared_6572_ = v_isSharedCheck_6603_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_val_6569_);
lean_dec(v_snd_6552_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6603_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v___x_6573_; 
v___x_6573_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_6569_, v___y_6560_);
lean_dec(v_val_6569_);
if (lean_obj_tag(v___x_6573_) == 0)
{
lean_object* v_a_6574_; lean_object* v___x_6575_; 
v_a_6574_ = lean_ctor_get(v___x_6573_, 0);
lean_inc(v_a_6574_);
lean_dec_ref_known(v___x_6573_, 1);
v___x_6575_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_6574_, v___y_6558_, v_compress_6515_, v___y_6560_, v___y_6561_);
if (lean_obj_tag(v___x_6575_) == 0)
{
lean_object* v_a_6576_; lean_object* v___x_6578_; uint8_t v_isShared_6579_; uint8_t v_isSharedCheck_6586_; 
v_a_6576_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6586_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6586_ == 0)
{
v___x_6578_ = v___x_6575_;
v_isShared_6579_ = v_isSharedCheck_6586_;
goto v_resetjp_6577_;
}
else
{
lean_inc(v_a_6576_);
lean_dec(v___x_6575_);
v___x_6578_ = lean_box(0);
v_isShared_6579_ = v_isSharedCheck_6586_;
goto v_resetjp_6577_;
}
v_resetjp_6577_:
{
lean_object* v___x_6581_; 
if (v_isShared_6572_ == 0)
{
lean_ctor_set_tag(v___x_6571_, 0);
lean_ctor_set(v___x_6571_, 0, v_a_6576_);
v___x_6581_ = v___x_6571_;
goto v_reusejp_6580_;
}
else
{
lean_object* v_reuseFailAlloc_6585_; 
v_reuseFailAlloc_6585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6585_, 0, v_a_6576_);
v___x_6581_ = v_reuseFailAlloc_6585_;
goto v_reusejp_6580_;
}
v_reusejp_6580_:
{
lean_object* v___x_6583_; 
if (v_isShared_6579_ == 0)
{
lean_ctor_set(v___x_6578_, 0, v___x_6581_);
v___x_6583_ = v___x_6578_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6584_; 
v_reuseFailAlloc_6584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6584_, 0, v___x_6581_);
v___x_6583_ = v_reuseFailAlloc_6584_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
return v___x_6583_;
}
}
}
}
else
{
lean_object* v_a_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6594_; 
lean_del_object(v___x_6571_);
v_a_6587_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6594_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6594_ == 0)
{
v___x_6589_ = v___x_6575_;
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_a_6587_);
lean_dec(v___x_6575_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v___x_6592_; 
if (v_isShared_6590_ == 0)
{
v___x_6592_ = v___x_6589_;
goto v_reusejp_6591_;
}
else
{
lean_object* v_reuseFailAlloc_6593_; 
v_reuseFailAlloc_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
v___x_6592_ = v_reuseFailAlloc_6593_;
goto v_reusejp_6591_;
}
v_reusejp_6591_:
{
return v___x_6592_;
}
}
}
}
else
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6602_; 
lean_del_object(v___x_6571_);
lean_dec(v___y_6558_);
v_a_6595_ = lean_ctor_get(v___x_6573_, 0);
v_isSharedCheck_6602_ = !lean_is_exclusive(v___x_6573_);
if (v_isSharedCheck_6602_ == 0)
{
v___x_6597_ = v___x_6573_;
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v___x_6573_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
v_resetjp_6596_:
{
lean_object* v___x_6600_; 
if (v_isShared_6598_ == 0)
{
v___x_6600_ = v___x_6597_;
goto v_reusejp_6599_;
}
else
{
lean_object* v_reuseFailAlloc_6601_; 
v_reuseFailAlloc_6601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6601_, 0, v_a_6595_);
v___x_6600_ = v_reuseFailAlloc_6601_;
goto v_reusejp_6599_;
}
v_reusejp_6599_:
{
return v___x_6600_;
}
}
}
}
}
else
{
lean_object* v___x_6604_; lean_object* v___x_6606_; 
lean_dec(v___y_6558_);
lean_dec(v_snd_6552_);
v___x_6604_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0));
if (v_isShared_6545_ == 0)
{
lean_ctor_set(v___x_6544_, 0, v___x_6604_);
v___x_6606_ = v___x_6544_;
goto v_reusejp_6605_;
}
else
{
lean_object* v_reuseFailAlloc_6607_; 
v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6607_, 0, v___x_6604_);
v___x_6606_ = v_reuseFailAlloc_6607_;
goto v_reusejp_6605_;
}
v_reusejp_6605_:
{
return v___x_6606_;
}
}
}
}
v_resetjp_6627_:
{
lean_object* v___y_6631_; 
if (v_isRec_6513_ == 0)
{
lean_object* v___x_6716_; lean_object* v___x_6717_; 
v___x_6716_ = lean_unsigned_to_nat(1u);
v___x_6717_ = lean_nat_sub(v___x_6609_, v___x_6716_);
v___y_6631_ = v___x_6717_;
goto v___jp_6630_;
}
else
{
lean_inc(v___x_6609_);
v___y_6631_ = v___x_6609_;
goto v___jp_6630_;
}
v___jp_6630_:
{
lean_object* v___x_6632_; lean_object* v___x_6634_; 
v___x_6632_ = lean_nat_add(v_numBranches_6626_, v___y_6631_);
lean_dec(v___y_6631_);
lean_dec(v_numBranches_6626_);
if (v_isShared_6629_ == 0)
{
lean_ctor_set(v___x_6628_, 15, v___x_6632_);
v___x_6634_ = v___x_6628_;
goto v_reusejp_6633_;
}
else
{
lean_object* v_reuseFailAlloc_6715_; 
v_reuseFailAlloc_6715_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_6715_, 0, v_congrThms_6611_);
lean_ctor_set(v_reuseFailAlloc_6715_, 1, v_simp_6612_);
lean_ctor_set(v_reuseFailAlloc_6715_, 2, v_symSimp_6613_);
lean_ctor_set(v_reuseFailAlloc_6715_, 3, v_symDSimp_6614_);
lean_ctor_set(v_reuseFailAlloc_6715_, 4, v_lastTag_6615_);
lean_ctor_set(v_reuseFailAlloc_6715_, 5, v_counters_6616_);
lean_ctor_set(v_reuseFailAlloc_6715_, 6, v_splitDiags_6617_);
lean_ctor_set(v_reuseFailAlloc_6715_, 7, v_ematchDiags_6618_);
lean_ctor_set(v_reuseFailAlloc_6715_, 8, v_lawfulEqCmpMap_6619_);
lean_ctor_set(v_reuseFailAlloc_6715_, 9, v_reflCmpMap_6620_);
lean_ctor_set(v_reuseFailAlloc_6715_, 10, v_anchors_6621_);
lean_ctor_set(v_reuseFailAlloc_6715_, 11, v_fvarAnchors_6622_);
lean_ctor_set(v_reuseFailAlloc_6715_, 12, v_instanceMap_6623_);
lean_ctor_set(v_reuseFailAlloc_6715_, 13, v_hoistedDecls_6624_);
lean_ctor_set(v_reuseFailAlloc_6715_, 14, v_proofInfos_6625_);
lean_ctor_set(v_reuseFailAlloc_6715_, 15, v___x_6632_);
v___x_6634_ = v_reuseFailAlloc_6715_;
goto v_reusejp_6633_;
}
v_reusejp_6633_:
{
lean_object* v___x_6635_; lean_object* v_toGoalState_6636_; lean_object* v_mvarId_6637_; lean_object* v_goalStack_6638_; lean_object* v___x_6640_; 
v___x_6635_ = lean_st_ref_put(v___y_6520_, v___x_6634_);
v_toGoalState_6636_ = lean_ctor_get(v_snd_6547_, 0);
v_mvarId_6637_ = lean_ctor_get(v_snd_6547_, 1);
lean_inc_n(v_mvarId_6637_, 2);
v_goalStack_6638_ = lean_ctor_get(v_toGoalState_6636_, 18);
lean_inc_ref(v_goalStack_6638_);
lean_inc_ref(v_toGoalState_6636_);
if (v_isShared_6555_ == 0)
{
lean_ctor_set(v___x_6554_, 1, v_toGoalState_6636_);
lean_ctor_set(v___x_6554_, 0, v_mvarId_6637_);
v___x_6640_ = v___x_6554_;
goto v_reusejp_6639_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_mvarId_6637_);
lean_ctor_set(v_reuseFailAlloc_6714_, 1, v_toGoalState_6636_);
v___x_6640_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6639_;
}
v_reusejp_6639_:
{
lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; 
lean_inc_ref(v_goalStack_6638_);
v___x_6641_ = lean_array_push(v_goalStack_6638_, v___x_6640_);
lean_inc_ref(v_c_6511_);
v___x_6642_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_6642_, 0, v_c_6511_);
lean_inc(v_mvarId_6637_);
v___x_6643_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6637_, v___x_6642_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
if (lean_obj_tag(v___x_6643_) == 0)
{
lean_object* v_a_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; uint64_t v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6653_; 
v_a_6644_ = lean_ctor_get(v___x_6643_, 0);
lean_inc(v_a_6644_);
lean_dec_ref_known(v___x_6643_, 1);
v___x_6645_ = lean_unsigned_to_nat(0u);
v___x_6646_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1));
v___x_6647_ = lean_unbox_uint64(v_a_6644_);
lean_dec(v_a_6644_);
lean_inc_n(v___x_6609_, 2);
lean_inc_ref(v_toGoalState_6636_);
v___x_6648_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_toGoalState_6636_, v_c_6511_, v___x_6536_, v___x_6609_, v___x_6641_, v___x_6647_, v_fst_6551_, v___x_6646_);
lean_dec_ref(v_c_6511_);
v___x_6649_ = lean_box(0);
v___x_6650_ = lean_unsigned_to_nat(1u);
v___x_6651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6651_, 0, v___x_6645_);
lean_ctor_set(v___x_6651_, 1, v___x_6609_);
lean_ctor_set(v___x_6651_, 2, v___x_6650_);
if (v_isShared_6550_ == 0)
{
lean_ctor_set(v___x_6549_, 1, v___x_6651_);
lean_ctor_set(v___x_6549_, 0, v___x_6649_);
v___x_6653_ = v___x_6549_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6705_; 
v_reuseFailAlloc_6705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6705_, 0, v___x_6649_);
lean_ctor_set(v_reuseFailAlloc_6705_, 1, v___x_6651_);
v___x_6653_ = v_reuseFailAlloc_6705_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; 
v___x_6654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6654_, 0, v___x_6646_);
lean_ctor_set(v___x_6654_, 1, v___x_6653_);
v___x_6655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6655_, 0, v___x_6646_);
lean_ctor_set(v___x_6655_, 1, v___x_6654_);
v___x_6656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6656_, 0, v___x_6649_);
lean_ctor_set(v___x_6656_, 1, v___x_6655_);
lean_inc(v_mvarId_6637_);
v___x_6657_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6516_, v_a_6532_, v_goal_6510_, v___x_6609_, v_snd_6547_, v_mvarId_6637_, v_stopAtFirstFailure_6517_, v_goalStack_6638_, v___x_6648_, v___x_6656_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
lean_dec(v___x_6648_);
lean_dec_ref(v_goalStack_6638_);
lean_dec(v___x_6609_);
if (lean_obj_tag(v___x_6657_) == 0)
{
lean_object* v_a_6658_; lean_object* v___x_6660_; uint8_t v_isShared_6661_; uint8_t v_isSharedCheck_6696_; 
v_a_6658_ = lean_ctor_get(v___x_6657_, 0);
v_isSharedCheck_6696_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6696_ == 0)
{
v___x_6660_ = v___x_6657_;
v_isShared_6661_ = v_isSharedCheck_6696_;
goto v_resetjp_6659_;
}
else
{
lean_inc(v_a_6658_);
lean_dec(v___x_6657_);
v___x_6660_ = lean_box(0);
v_isShared_6661_ = v_isSharedCheck_6696_;
goto v_resetjp_6659_;
}
v_resetjp_6659_:
{
lean_object* v_fst_6662_; 
v_fst_6662_ = lean_ctor_get(v_a_6658_, 0);
if (lean_obj_tag(v_fst_6662_) == 0)
{
lean_object* v_snd_6663_; lean_object* v_snd_6664_; lean_object* v_fst_6665_; lean_object* v_fst_6666_; lean_object* v___x_6667_; 
lean_del_object(v___x_6660_);
v_snd_6663_ = lean_ctor_get(v_a_6658_, 1);
lean_inc(v_snd_6663_);
lean_dec(v_a_6658_);
v_snd_6664_ = lean_ctor_get(v_snd_6663_, 1);
lean_inc(v_snd_6664_);
v_fst_6665_ = lean_ctor_get(v_snd_6663_, 0);
lean_inc(v_fst_6665_);
lean_dec(v_snd_6663_);
v_fst_6666_ = lean_ctor_get(v_snd_6664_, 0);
lean_inc(v_fst_6666_);
lean_dec(v_snd_6664_);
lean_inc(v_mvarId_6637_);
v___x_6667_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6637_, v___f_6608_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
if (lean_obj_tag(v___x_6667_) == 0)
{
lean_object* v_a_6668_; lean_object* v___x_6669_; 
v_a_6668_ = lean_ctor_get(v___x_6667_, 0);
lean_inc(v_a_6668_);
lean_dec_ref_known(v___x_6667_, 1);
lean_inc(v_mvarId_6637_);
v___x_6669_ = l_Lean_MVarId_getType(v_mvarId_6637_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
if (lean_obj_tag(v___x_6669_) == 0)
{
lean_object* v_a_6670_; uint8_t v___x_6671_; 
v_a_6670_ = lean_ctor_get(v___x_6669_, 0);
lean_inc(v_a_6670_);
lean_dec_ref_known(v___x_6669_, 1);
v___x_6671_ = l_Lean_Expr_isFalse(v_a_6670_);
lean_dec(v_a_6670_);
if (v___x_6671_ == 0)
{
lean_object* v___x_6672_; 
v___x_6672_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6637_, v_a_6668_, v___y_6524_);
lean_dec_ref(v___x_6672_);
v___y_6557_ = v___x_6645_;
v___y_6558_ = v_fst_6665_;
v___y_6559_ = v_fst_6666_;
v___y_6560_ = v___y_6525_;
v___y_6561_ = v___y_6526_;
goto v___jp_6556_;
}
else
{
lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; 
v___x_6673_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_6674_ = l_Lean_Meta_mkExpectedPropHint(v_a_6668_, v___x_6673_);
v___x_6675_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6637_, v___x_6674_, v___y_6524_);
lean_dec_ref(v___x_6675_);
v___y_6557_ = v___x_6645_;
v___y_6558_ = v_fst_6665_;
v___y_6559_ = v_fst_6666_;
v___y_6560_ = v___y_6525_;
v___y_6561_ = v___y_6526_;
goto v___jp_6556_;
}
}
else
{
lean_object* v_a_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6683_; 
lean_dec(v_a_6668_);
lean_dec(v_fst_6666_);
lean_dec(v_fst_6665_);
lean_dec(v_mvarId_6637_);
lean_dec(v_snd_6552_);
lean_del_object(v___x_6544_);
v_a_6676_ = lean_ctor_get(v___x_6669_, 0);
v_isSharedCheck_6683_ = !lean_is_exclusive(v___x_6669_);
if (v_isSharedCheck_6683_ == 0)
{
v___x_6678_ = v___x_6669_;
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_a_6676_);
lean_dec(v___x_6669_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v___x_6681_; 
if (v_isShared_6679_ == 0)
{
v___x_6681_ = v___x_6678_;
goto v_reusejp_6680_;
}
else
{
lean_object* v_reuseFailAlloc_6682_; 
v_reuseFailAlloc_6682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6682_, 0, v_a_6676_);
v___x_6681_ = v_reuseFailAlloc_6682_;
goto v_reusejp_6680_;
}
v_reusejp_6680_:
{
return v___x_6681_;
}
}
}
}
else
{
lean_object* v_a_6684_; lean_object* v___x_6686_; uint8_t v_isShared_6687_; uint8_t v_isSharedCheck_6691_; 
lean_dec(v_fst_6666_);
lean_dec(v_fst_6665_);
lean_dec(v_mvarId_6637_);
lean_dec(v_snd_6552_);
lean_del_object(v___x_6544_);
v_a_6684_ = lean_ctor_get(v___x_6667_, 0);
v_isSharedCheck_6691_ = !lean_is_exclusive(v___x_6667_);
if (v_isSharedCheck_6691_ == 0)
{
v___x_6686_ = v___x_6667_;
v_isShared_6687_ = v_isSharedCheck_6691_;
goto v_resetjp_6685_;
}
else
{
lean_inc(v_a_6684_);
lean_dec(v___x_6667_);
v___x_6686_ = lean_box(0);
v_isShared_6687_ = v_isSharedCheck_6691_;
goto v_resetjp_6685_;
}
v_resetjp_6685_:
{
lean_object* v___x_6689_; 
if (v_isShared_6687_ == 0)
{
v___x_6689_ = v___x_6686_;
goto v_reusejp_6688_;
}
else
{
lean_object* v_reuseFailAlloc_6690_; 
v_reuseFailAlloc_6690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6690_, 0, v_a_6684_);
v___x_6689_ = v_reuseFailAlloc_6690_;
goto v_reusejp_6688_;
}
v_reusejp_6688_:
{
return v___x_6689_;
}
}
}
}
else
{
lean_object* v_val_6692_; lean_object* v___x_6694_; 
lean_inc_ref(v_fst_6662_);
lean_dec(v_a_6658_);
lean_dec(v_mvarId_6637_);
lean_dec_ref(v___f_6608_);
lean_dec(v_snd_6552_);
lean_del_object(v___x_6544_);
v_val_6692_ = lean_ctor_get(v_fst_6662_, 0);
lean_inc(v_val_6692_);
lean_dec_ref_known(v_fst_6662_, 1);
if (v_isShared_6661_ == 0)
{
lean_ctor_set(v___x_6660_, 0, v_val_6692_);
v___x_6694_ = v___x_6660_;
goto v_reusejp_6693_;
}
else
{
lean_object* v_reuseFailAlloc_6695_; 
v_reuseFailAlloc_6695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6695_, 0, v_val_6692_);
v___x_6694_ = v_reuseFailAlloc_6695_;
goto v_reusejp_6693_;
}
v_reusejp_6693_:
{
return v___x_6694_;
}
}
}
}
else
{
lean_object* v_a_6697_; lean_object* v___x_6699_; uint8_t v_isShared_6700_; uint8_t v_isSharedCheck_6704_; 
lean_dec(v_mvarId_6637_);
lean_dec_ref(v___f_6608_);
lean_dec(v_snd_6552_);
lean_del_object(v___x_6544_);
v_a_6697_ = lean_ctor_get(v___x_6657_, 0);
v_isSharedCheck_6704_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6704_ == 0)
{
v___x_6699_ = v___x_6657_;
v_isShared_6700_ = v_isSharedCheck_6704_;
goto v_resetjp_6698_;
}
else
{
lean_inc(v_a_6697_);
lean_dec(v___x_6657_);
v___x_6699_ = lean_box(0);
v_isShared_6700_ = v_isSharedCheck_6704_;
goto v_resetjp_6698_;
}
v_resetjp_6698_:
{
lean_object* v___x_6702_; 
if (v_isShared_6700_ == 0)
{
v___x_6702_ = v___x_6699_;
goto v_reusejp_6701_;
}
else
{
lean_object* v_reuseFailAlloc_6703_; 
v_reuseFailAlloc_6703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6703_, 0, v_a_6697_);
v___x_6702_ = v_reuseFailAlloc_6703_;
goto v_reusejp_6701_;
}
v_reusejp_6701_:
{
return v___x_6702_;
}
}
}
}
}
else
{
lean_object* v_a_6706_; lean_object* v___x_6708_; uint8_t v_isShared_6709_; uint8_t v_isSharedCheck_6713_; 
lean_dec_ref(v___x_6641_);
lean_dec_ref(v_goalStack_6638_);
lean_dec(v_mvarId_6637_);
lean_dec(v___x_6609_);
lean_dec_ref(v___f_6608_);
lean_dec(v_snd_6552_);
lean_dec(v_fst_6551_);
lean_del_object(v___x_6549_);
lean_dec(v_snd_6547_);
lean_del_object(v___x_6544_);
lean_dec_ref(v___x_6536_);
lean_dec(v_a_6532_);
lean_dec_ref(v_kp_6516_);
lean_dec_ref(v_c_6511_);
lean_dec_ref(v_goal_6510_);
v_a_6706_ = lean_ctor_get(v___x_6643_, 0);
v_isSharedCheck_6713_ = !lean_is_exclusive(v___x_6643_);
if (v_isSharedCheck_6713_ == 0)
{
v___x_6708_ = v___x_6643_;
v_isShared_6709_ = v_isSharedCheck_6713_;
goto v_resetjp_6707_;
}
else
{
lean_inc(v_a_6706_);
lean_dec(v___x_6643_);
v___x_6708_ = lean_box(0);
v_isShared_6709_ = v_isSharedCheck_6713_;
goto v_resetjp_6707_;
}
v_resetjp_6707_:
{
lean_object* v___x_6711_; 
if (v_isShared_6709_ == 0)
{
v___x_6711_ = v___x_6708_;
goto v_reusejp_6710_;
}
else
{
lean_object* v_reuseFailAlloc_6712_; 
v_reuseFailAlloc_6712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6706_);
v___x_6711_ = v_reuseFailAlloc_6712_;
goto v_reusejp_6710_;
}
v_reusejp_6710_:
{
return v___x_6711_;
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
lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6729_; 
lean_dec_ref(v___x_6536_);
lean_dec(v_a_6534_);
lean_dec(v_a_6532_);
lean_dec_ref(v_kp_6516_);
lean_dec_ref(v_c_6511_);
lean_dec_ref(v_goal_6510_);
v_a_6722_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6729_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6729_ == 0)
{
v___x_6724_ = v___x_6541_;
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_dec(v___x_6541_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6727_; 
if (v_isShared_6725_ == 0)
{
v___x_6727_ = v___x_6724_;
goto v_reusejp_6726_;
}
else
{
lean_object* v_reuseFailAlloc_6728_; 
v_reuseFailAlloc_6728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6728_, 0, v_a_6722_);
v___x_6727_ = v_reuseFailAlloc_6728_;
goto v_reusejp_6726_;
}
v_reusejp_6726_:
{
return v___x_6727_;
}
}
}
}
else
{
lean_object* v_a_6730_; lean_object* v___x_6732_; uint8_t v_isShared_6733_; uint8_t v_isSharedCheck_6737_; 
lean_dec(v_a_6532_);
lean_dec_ref(v_kp_6516_);
lean_dec(v_candidates_x3f_6514_);
lean_dec(v_numCases_6512_);
lean_dec_ref(v_c_6511_);
lean_dec_ref(v_goal_6510_);
v_a_6730_ = lean_ctor_get(v___x_6533_, 0);
v_isSharedCheck_6737_ = !lean_is_exclusive(v___x_6533_);
if (v_isSharedCheck_6737_ == 0)
{
v___x_6732_ = v___x_6533_;
v_isShared_6733_ = v_isSharedCheck_6737_;
goto v_resetjp_6731_;
}
else
{
lean_inc(v_a_6730_);
lean_dec(v___x_6533_);
v___x_6732_ = lean_box(0);
v_isShared_6733_ = v_isSharedCheck_6737_;
goto v_resetjp_6731_;
}
v_resetjp_6731_:
{
lean_object* v___x_6735_; 
if (v_isShared_6733_ == 0)
{
v___x_6735_ = v___x_6732_;
goto v_reusejp_6734_;
}
else
{
lean_object* v_reuseFailAlloc_6736_; 
v_reuseFailAlloc_6736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6736_, 0, v_a_6730_);
v___x_6735_ = v_reuseFailAlloc_6736_;
goto v_reusejp_6734_;
}
v_reusejp_6734_:
{
return v___x_6735_;
}
}
}
}
else
{
lean_object* v_a_6738_; lean_object* v___x_6740_; uint8_t v_isShared_6741_; uint8_t v_isSharedCheck_6745_; 
lean_dec_ref(v_kp_6516_);
lean_dec(v_candidates_x3f_6514_);
lean_dec(v_numCases_6512_);
lean_dec_ref(v_c_6511_);
lean_dec_ref(v_goal_6510_);
v_a_6738_ = lean_ctor_get(v___x_6531_, 0);
v_isSharedCheck_6745_ = !lean_is_exclusive(v___x_6531_);
if (v_isSharedCheck_6745_ == 0)
{
v___x_6740_ = v___x_6531_;
v_isShared_6741_ = v_isSharedCheck_6745_;
goto v_resetjp_6739_;
}
else
{
lean_inc(v_a_6738_);
lean_dec(v___x_6531_);
v___x_6740_ = lean_box(0);
v_isShared_6741_ = v_isSharedCheck_6745_;
goto v_resetjp_6739_;
}
v_resetjp_6739_:
{
lean_object* v___x_6743_; 
if (v_isShared_6741_ == 0)
{
v___x_6743_ = v___x_6740_;
goto v_reusejp_6742_;
}
else
{
lean_object* v_reuseFailAlloc_6744_; 
v_reuseFailAlloc_6744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6744_, 0, v_a_6738_);
v___x_6743_ = v_reuseFailAlloc_6744_;
goto v_reusejp_6742_;
}
v_reusejp_6742_:
{
return v___x_6743_;
}
}
}
}
else
{
lean_object* v_a_6746_; lean_object* v___x_6748_; uint8_t v_isShared_6749_; uint8_t v_isSharedCheck_6753_; 
lean_dec_ref(v_kp_6516_);
lean_dec(v_candidates_x3f_6514_);
lean_dec(v_numCases_6512_);
lean_dec_ref(v_c_6511_);
lean_dec_ref(v_goal_6510_);
v_a_6746_ = lean_ctor_get(v___x_6528_, 0);
v_isSharedCheck_6753_ = !lean_is_exclusive(v___x_6528_);
if (v_isSharedCheck_6753_ == 0)
{
v___x_6748_ = v___x_6528_;
v_isShared_6749_ = v_isSharedCheck_6753_;
goto v_resetjp_6747_;
}
else
{
lean_inc(v_a_6746_);
lean_dec(v___x_6528_);
v___x_6748_ = lean_box(0);
v_isShared_6749_ = v_isSharedCheck_6753_;
goto v_resetjp_6747_;
}
v_resetjp_6747_:
{
lean_object* v___x_6751_; 
if (v_isShared_6749_ == 0)
{
v___x_6751_ = v___x_6748_;
goto v_reusejp_6750_;
}
else
{
lean_object* v_reuseFailAlloc_6752_; 
v_reuseFailAlloc_6752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6752_, 0, v_a_6746_);
v___x_6751_ = v_reuseFailAlloc_6752_;
goto v_reusejp_6750_;
}
v_reusejp_6750_:
{
return v___x_6751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_goal_6754_ = _args[0];
lean_object* v_c_6755_ = _args[1];
lean_object* v_numCases_6756_ = _args[2];
lean_object* v_isRec_6757_ = _args[3];
lean_object* v_candidates_x3f_6758_ = _args[4];
lean_object* v_compress_6759_ = _args[5];
lean_object* v_kp_6760_ = _args[6];
lean_object* v_stopAtFirstFailure_6761_ = _args[7];
lean_object* v___y_6762_ = _args[8];
lean_object* v___y_6763_ = _args[9];
lean_object* v___y_6764_ = _args[10];
lean_object* v___y_6765_ = _args[11];
lean_object* v___y_6766_ = _args[12];
lean_object* v___y_6767_ = _args[13];
lean_object* v___y_6768_ = _args[14];
lean_object* v___y_6769_ = _args[15];
lean_object* v___y_6770_ = _args[16];
lean_object* v___y_6771_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6772_; uint8_t v_compress_boxed_6773_; uint8_t v_stopAtFirstFailure_boxed_6774_; lean_object* v_res_6775_; 
v_isRec_boxed_6772_ = lean_unbox(v_isRec_6757_);
v_compress_boxed_6773_ = lean_unbox(v_compress_6759_);
v_stopAtFirstFailure_boxed_6774_ = lean_unbox(v_stopAtFirstFailure_6761_);
v_res_6775_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(v_goal_6754_, v_c_6755_, v_numCases_6756_, v_isRec_boxed_6772_, v_candidates_x3f_6758_, v_compress_boxed_6773_, v_kp_6760_, v_stopAtFirstFailure_boxed_6774_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_);
lean_dec(v___y_6770_);
lean_dec_ref(v___y_6769_);
lean_dec(v___y_6768_);
lean_dec_ref(v___y_6767_);
lean_dec(v___y_6766_);
lean_dec_ref(v___y_6765_);
lean_dec(v___y_6764_);
lean_dec_ref(v___y_6763_);
lean_dec(v___y_6762_);
return v_res_6775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_6776_, lean_object* v_numCases_6777_, uint8_t v_isRec_6778_, uint8_t v_stopAtFirstFailure_6779_, uint8_t v_compress_6780_, lean_object* v_candidates_x3f_6781_, lean_object* v_goal_6782_, lean_object* v_kp_6783_, lean_object* v_a_6784_, lean_object* v_a_6785_, lean_object* v_a_6786_, lean_object* v_a_6787_, lean_object* v_a_6788_, lean_object* v_a_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_, lean_object* v_a_6792_){
_start:
{
lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___f_6797_; lean_object* v___x_6798_; 
v___x_6794_ = lean_box(v_isRec_6778_);
v___x_6795_ = lean_box(v_compress_6780_);
v___x_6796_ = lean_box(v_stopAtFirstFailure_6779_);
lean_inc_ref(v_goal_6782_);
v___f_6797_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed), 18, 8);
lean_closure_set(v___f_6797_, 0, v_goal_6782_);
lean_closure_set(v___f_6797_, 1, v_c_6776_);
lean_closure_set(v___f_6797_, 2, v_numCases_6777_);
lean_closure_set(v___f_6797_, 3, v___x_6794_);
lean_closure_set(v___f_6797_, 4, v_candidates_x3f_6781_);
lean_closure_set(v___f_6797_, 5, v___x_6795_);
lean_closure_set(v___f_6797_, 6, v_kp_6783_);
lean_closure_set(v___f_6797_, 7, v___x_6796_);
v___x_6798_ = l_Lean_Meta_Grind_withHoistedDecls___redArg(v_goal_6782_, v___f_6797_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_);
return v___x_6798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6799_ = _args[0];
lean_object* v_numCases_6800_ = _args[1];
lean_object* v_isRec_6801_ = _args[2];
lean_object* v_stopAtFirstFailure_6802_ = _args[3];
lean_object* v_compress_6803_ = _args[4];
lean_object* v_candidates_x3f_6804_ = _args[5];
lean_object* v_goal_6805_ = _args[6];
lean_object* v_kp_6806_ = _args[7];
lean_object* v_a_6807_ = _args[8];
lean_object* v_a_6808_ = _args[9];
lean_object* v_a_6809_ = _args[10];
lean_object* v_a_6810_ = _args[11];
lean_object* v_a_6811_ = _args[12];
lean_object* v_a_6812_ = _args[13];
lean_object* v_a_6813_ = _args[14];
lean_object* v_a_6814_ = _args[15];
lean_object* v_a_6815_ = _args[16];
lean_object* v_a_6816_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6817_; uint8_t v_stopAtFirstFailure_boxed_6818_; uint8_t v_compress_boxed_6819_; lean_object* v_res_6820_; 
v_isRec_boxed_6817_ = lean_unbox(v_isRec_6801_);
v_stopAtFirstFailure_boxed_6818_ = lean_unbox(v_stopAtFirstFailure_6802_);
v_compress_boxed_6819_ = lean_unbox(v_compress_6803_);
v_res_6820_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6799_, v_numCases_6800_, v_isRec_boxed_6817_, v_stopAtFirstFailure_boxed_6818_, v_compress_boxed_6819_, v_candidates_x3f_6804_, v_goal_6805_, v_kp_6806_, v_a_6807_, v_a_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_);
lean_dec(v_a_6815_);
lean_dec_ref(v_a_6814_);
lean_dec(v_a_6813_);
lean_dec_ref(v_a_6812_);
lean_dec(v_a_6811_);
lean_dec_ref(v_a_6810_);
lean_dec(v_a_6809_);
lean_dec_ref(v_a_6808_);
lean_dec(v_a_6807_);
return v_res_6820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6821_, lean_object* v_numCases_6822_, uint8_t v_isRec_6823_, uint8_t v_stopAtFirstFailure_6824_, uint8_t v_compress_6825_, lean_object* v_candidates_x3f_6826_, lean_object* v_goal_6827_, lean_object* v_x_6828_, lean_object* v_kp_6829_, lean_object* v_a_6830_, lean_object* v_a_6831_, lean_object* v_a_6832_, lean_object* v_a_6833_, lean_object* v_a_6834_, lean_object* v_a_6835_, lean_object* v_a_6836_, lean_object* v_a_6837_, lean_object* v_a_6838_){
_start:
{
lean_object* v___x_6840_; 
v___x_6840_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6821_, v_numCases_6822_, v_isRec_6823_, v_stopAtFirstFailure_6824_, v_compress_6825_, v_candidates_x3f_6826_, v_goal_6827_, v_kp_6829_, v_a_6830_, v_a_6831_, v_a_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_);
return v___x_6840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6841_ = _args[0];
lean_object* v_numCases_6842_ = _args[1];
lean_object* v_isRec_6843_ = _args[2];
lean_object* v_stopAtFirstFailure_6844_ = _args[3];
lean_object* v_compress_6845_ = _args[4];
lean_object* v_candidates_x3f_6846_ = _args[5];
lean_object* v_goal_6847_ = _args[6];
lean_object* v_x_6848_ = _args[7];
lean_object* v_kp_6849_ = _args[8];
lean_object* v_a_6850_ = _args[9];
lean_object* v_a_6851_ = _args[10];
lean_object* v_a_6852_ = _args[11];
lean_object* v_a_6853_ = _args[12];
lean_object* v_a_6854_ = _args[13];
lean_object* v_a_6855_ = _args[14];
lean_object* v_a_6856_ = _args[15];
lean_object* v_a_6857_ = _args[16];
lean_object* v_a_6858_ = _args[17];
lean_object* v_a_6859_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6860_; uint8_t v_stopAtFirstFailure_boxed_6861_; uint8_t v_compress_boxed_6862_; lean_object* v_res_6863_; 
v_isRec_boxed_6860_ = lean_unbox(v_isRec_6843_);
v_stopAtFirstFailure_boxed_6861_ = lean_unbox(v_stopAtFirstFailure_6844_);
v_compress_boxed_6862_ = lean_unbox(v_compress_6845_);
v_res_6863_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6841_, v_numCases_6842_, v_isRec_boxed_6860_, v_stopAtFirstFailure_boxed_6861_, v_compress_boxed_6862_, v_candidates_x3f_6846_, v_goal_6847_, v_x_6848_, v_kp_6849_, v_a_6850_, v_a_6851_, v_a_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_, v_a_6857_, v_a_6858_);
lean_dec(v_a_6858_);
lean_dec_ref(v_a_6857_);
lean_dec(v_a_6856_);
lean_dec_ref(v_a_6855_);
lean_dec(v_a_6854_);
lean_dec_ref(v_a_6853_);
lean_dec(v_a_6852_);
lean_dec_ref(v_a_6851_);
lean_dec(v_a_6850_);
lean_dec_ref(v_x_6848_);
return v_res_6863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_6864_, lean_object* v_a_6865_, lean_object* v_goal_6866_, lean_object* v___x_6867_, lean_object* v_snd_6868_, lean_object* v___x_6869_, uint8_t v_stopAtFirstFailure_6870_, lean_object* v___x_6871_, lean_object* v_as_6872_, lean_object* v_as_x27_6873_, lean_object* v_b_6874_, lean_object* v_a_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_, lean_object* v___y_6884_){
_start:
{
lean_object* v___x_6886_; 
v___x_6886_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6864_, v_a_6865_, v_goal_6866_, v___x_6867_, v_snd_6868_, v___x_6869_, v_stopAtFirstFailure_6870_, v___x_6871_, v_as_x27_6873_, v_b_6874_, v___y_6876_, v___y_6877_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_);
return v___x_6886_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6887_ = _args[0];
lean_object* v_a_6888_ = _args[1];
lean_object* v_goal_6889_ = _args[2];
lean_object* v___x_6890_ = _args[3];
lean_object* v_snd_6891_ = _args[4];
lean_object* v___x_6892_ = _args[5];
lean_object* v_stopAtFirstFailure_6893_ = _args[6];
lean_object* v___x_6894_ = _args[7];
lean_object* v_as_6895_ = _args[8];
lean_object* v_as_x27_6896_ = _args[9];
lean_object* v_b_6897_ = _args[10];
lean_object* v_a_6898_ = _args[11];
lean_object* v___y_6899_ = _args[12];
lean_object* v___y_6900_ = _args[13];
lean_object* v___y_6901_ = _args[14];
lean_object* v___y_6902_ = _args[15];
lean_object* v___y_6903_ = _args[16];
lean_object* v___y_6904_ = _args[17];
lean_object* v___y_6905_ = _args[18];
lean_object* v___y_6906_ = _args[19];
lean_object* v___y_6907_ = _args[20];
lean_object* v___y_6908_ = _args[21];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6909_; lean_object* v_res_6910_; 
v_stopAtFirstFailure_boxed_6909_ = lean_unbox(v_stopAtFirstFailure_6893_);
v_res_6910_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6887_, v_a_6888_, v_goal_6889_, v___x_6890_, v_snd_6891_, v___x_6892_, v_stopAtFirstFailure_boxed_6909_, v___x_6894_, v_as_6895_, v_as_x27_6896_, v_b_6897_, v_a_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_);
lean_dec(v___y_6907_);
lean_dec_ref(v___y_6906_);
lean_dec(v___y_6905_);
lean_dec_ref(v___y_6904_);
lean_dec(v___y_6903_);
lean_dec_ref(v___y_6902_);
lean_dec(v___y_6901_);
lean_dec_ref(v___y_6900_);
lean_dec(v___y_6899_);
lean_dec(v_as_x27_6896_);
lean_dec(v_as_6895_);
lean_dec_ref(v___x_6894_);
lean_dec(v___x_6890_);
return v_res_6910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_mvarId_6911_, lean_object* v_val_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_){
_start:
{
lean_object* v___x_6923_; 
v___x_6923_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6911_, v_val_6912_, v___y_6919_);
return v___x_6923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_mvarId_6924_, lean_object* v_val_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_){
_start:
{
lean_object* v_res_6936_; 
v_res_6936_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_mvarId_6924_, v_val_6925_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_, v___y_6934_);
lean_dec(v___y_6934_);
lean_dec_ref(v___y_6933_);
lean_dec(v___y_6932_);
lean_dec_ref(v___y_6931_);
lean_dec(v___y_6930_);
lean_dec_ref(v___y_6929_);
lean_dec(v___y_6928_);
lean_dec_ref(v___y_6927_);
lean_dec(v___y_6926_);
return v_res_6936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4(lean_object* v_00_u03b2_6937_, lean_object* v_x_6938_, lean_object* v_x_6939_, lean_object* v_x_6940_){
_start:
{
lean_object* v___x_6941_; 
v___x_6941_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_x_6938_, v_x_6939_, v_x_6940_);
return v___x_6941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(lean_object* v_00_u03b2_6942_, lean_object* v_x_6943_, size_t v_x_6944_, size_t v_x_6945_, lean_object* v_x_6946_, lean_object* v_x_6947_){
_start:
{
lean_object* v___x_6948_; 
v___x_6948_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6943_, v_x_6944_, v_x_6945_, v_x_6946_, v_x_6947_);
return v___x_6948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b2_6949_, lean_object* v_x_6950_, lean_object* v_x_6951_, lean_object* v_x_6952_, lean_object* v_x_6953_, lean_object* v_x_6954_){
_start:
{
size_t v_x_118983__boxed_6955_; size_t v_x_118984__boxed_6956_; lean_object* v_res_6957_; 
v_x_118983__boxed_6955_ = lean_unbox_usize(v_x_6951_);
lean_dec(v_x_6951_);
v_x_118984__boxed_6956_ = lean_unbox_usize(v_x_6952_);
lean_dec(v_x_6952_);
v_res_6957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(v_00_u03b2_6949_, v_x_6950_, v_x_118983__boxed_6955_, v_x_118984__boxed_6956_, v_x_6953_, v_x_6954_);
return v_res_6957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_6958_, lean_object* v_n_6959_, lean_object* v_k_6960_, lean_object* v_v_6961_){
_start:
{
lean_object* v___x_6962_; 
v___x_6962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v_n_6959_, v_k_6960_, v_v_6961_);
return v___x_6962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_6963_, size_t v_depth_6964_, lean_object* v_keys_6965_, lean_object* v_vals_6966_, lean_object* v_heq_6967_, lean_object* v_i_6968_, lean_object* v_entries_6969_){
_start:
{
lean_object* v___x_6970_; 
v___x_6970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_6964_, v_keys_6965_, v_vals_6966_, v_i_6968_, v_entries_6969_);
return v___x_6970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_6971_, lean_object* v_depth_6972_, lean_object* v_keys_6973_, lean_object* v_vals_6974_, lean_object* v_heq_6975_, lean_object* v_i_6976_, lean_object* v_entries_6977_){
_start:
{
size_t v_depth_boxed_6978_; lean_object* v_res_6979_; 
v_depth_boxed_6978_ = lean_unbox_usize(v_depth_6972_);
lean_dec(v_depth_6972_);
v_res_6979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(v_00_u03b2_6971_, v_depth_boxed_6978_, v_keys_6973_, v_vals_6974_, v_heq_6975_, v_i_6976_, v_entries_6977_);
lean_dec_ref(v_vals_6974_);
lean_dec_ref(v_keys_6973_);
return v_res_6979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6980_, lean_object* v_x_6981_, lean_object* v_x_6982_, lean_object* v_x_6983_, lean_object* v_x_6984_){
_start:
{
lean_object* v___x_6985_; 
v___x_6985_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_x_6981_, v_x_6982_, v_x_6983_, v_x_6984_);
return v___x_6985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_){
_start:
{
lean_object* v___x_6999_; 
v___x_6999_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6986_, v___y_6988_, v___y_6989_, v___y_6990_, v___y_6991_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_, v___y_6996_, v___y_6997_);
return v___x_6999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_){
_start:
{
lean_object* v_res_7013_; 
v_res_7013_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
lean_dec(v___y_7011_);
lean_dec_ref(v___y_7010_);
lean_dec(v___y_7009_);
lean_dec_ref(v___y_7008_);
lean_dec(v___y_7007_);
lean_dec_ref(v___y_7006_);
lean_dec(v___y_7005_);
lean_dec_ref(v___y_7004_);
lean_dec(v___y_7003_);
lean_dec_ref(v___y_7001_);
return v_res_7013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_7014_, lean_object* v___y_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_){
_start:
{
lean_object* v___x_7025_; lean_object* v___x_7026_; 
v___x_7025_ = lean_st_mk_ref(v_goal_7014_);
v___x_7026_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_7025_, v___y_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_, v___y_7023_);
if (lean_obj_tag(v___x_7026_) == 0)
{
lean_object* v_a_7027_; lean_object* v___x_7029_; uint8_t v_isShared_7030_; uint8_t v_isSharedCheck_7036_; 
v_a_7027_ = lean_ctor_get(v___x_7026_, 0);
v_isSharedCheck_7036_ = !lean_is_exclusive(v___x_7026_);
if (v_isSharedCheck_7036_ == 0)
{
v___x_7029_ = v___x_7026_;
v_isShared_7030_ = v_isSharedCheck_7036_;
goto v_resetjp_7028_;
}
else
{
lean_inc(v_a_7027_);
lean_dec(v___x_7026_);
v___x_7029_ = lean_box(0);
v_isShared_7030_ = v_isSharedCheck_7036_;
goto v_resetjp_7028_;
}
v_resetjp_7028_:
{
lean_object* v___x_7031_; lean_object* v___x_7032_; lean_object* v___x_7034_; 
v___x_7031_ = lean_st_ref_get(v___x_7025_);
lean_dec(v___x_7025_);
v___x_7032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7032_, 0, v_a_7027_);
lean_ctor_set(v___x_7032_, 1, v___x_7031_);
if (v_isShared_7030_ == 0)
{
lean_ctor_set(v___x_7029_, 0, v___x_7032_);
v___x_7034_ = v___x_7029_;
goto v_reusejp_7033_;
}
else
{
lean_object* v_reuseFailAlloc_7035_; 
v_reuseFailAlloc_7035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7035_, 0, v___x_7032_);
v___x_7034_ = v_reuseFailAlloc_7035_;
goto v_reusejp_7033_;
}
v_reusejp_7033_:
{
return v___x_7034_;
}
}
}
else
{
lean_object* v_a_7037_; lean_object* v___x_7039_; uint8_t v_isShared_7040_; uint8_t v_isSharedCheck_7044_; 
lean_dec(v___x_7025_);
v_a_7037_ = lean_ctor_get(v___x_7026_, 0);
v_isSharedCheck_7044_ = !lean_is_exclusive(v___x_7026_);
if (v_isSharedCheck_7044_ == 0)
{
v___x_7039_ = v___x_7026_;
v_isShared_7040_ = v_isSharedCheck_7044_;
goto v_resetjp_7038_;
}
else
{
lean_inc(v_a_7037_);
lean_dec(v___x_7026_);
v___x_7039_ = lean_box(0);
v_isShared_7040_ = v_isSharedCheck_7044_;
goto v_resetjp_7038_;
}
v_resetjp_7038_:
{
lean_object* v___x_7042_; 
if (v_isShared_7040_ == 0)
{
v___x_7042_ = v___x_7039_;
goto v_reusejp_7041_;
}
else
{
lean_object* v_reuseFailAlloc_7043_; 
v_reuseFailAlloc_7043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7043_, 0, v_a_7037_);
v___x_7042_ = v_reuseFailAlloc_7043_;
goto v_reusejp_7041_;
}
v_reusejp_7041_:
{
return v___x_7042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_7045_, lean_object* v___y_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_){
_start:
{
lean_object* v_res_7056_; 
v_res_7056_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_);
lean_dec(v___y_7054_);
lean_dec_ref(v___y_7053_);
lean_dec(v___y_7052_);
lean_dec_ref(v___y_7051_);
lean_dec(v___y_7050_);
lean_dec_ref(v___y_7049_);
lean_dec(v___y_7048_);
lean_dec_ref(v___y_7047_);
lean_dec(v___y_7046_);
return v_res_7056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_7057_, lean_object* v___f_7058_, lean_object* v___y_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_, lean_object* v___y_7065_, lean_object* v___y_7066_, lean_object* v___y_7067_, lean_object* v___y_7068_, lean_object* v___y_7069_, lean_object* v___y_7070_){
_start:
{
lean_object* v___x_7072_; lean_object* v___x_7073_; 
v___x_7072_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_7072_, 0, v___y_7057_);
v___x_7073_ = l_Lean_Meta_Grind_Action_andThen(v___x_7072_, v___f_7058_, v___y_7059_, v___y_7060_, v___y_7061_, v___y_7062_, v___y_7063_, v___y_7064_, v___y_7065_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_, v___y_7070_);
return v___x_7073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_7074_, lean_object* v___f_7075_, lean_object* v___y_7076_, lean_object* v___y_7077_, lean_object* v___y_7078_, lean_object* v___y_7079_, lean_object* v___y_7080_, lean_object* v___y_7081_, lean_object* v___y_7082_, lean_object* v___y_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_){
_start:
{
lean_object* v_res_7089_; 
v_res_7089_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_7074_, v___f_7075_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_, v___y_7080_, v___y_7081_, v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_);
lean_dec(v___y_7087_);
lean_dec_ref(v___y_7086_);
lean_dec(v___y_7085_);
lean_dec_ref(v___y_7084_);
lean_dec(v___y_7083_);
lean_dec_ref(v___y_7082_);
lean_dec(v___y_7081_);
lean_dec_ref(v___y_7080_);
lean_dec(v___y_7079_);
return v_res_7089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_7091_, uint8_t v_compress_7092_, lean_object* v_goal_7093_, lean_object* v_kna_7094_, lean_object* v_kp_7095_, lean_object* v_a_7096_, lean_object* v_a_7097_, lean_object* v_a_7098_, lean_object* v_a_7099_, lean_object* v_a_7100_, lean_object* v_a_7101_, lean_object* v_a_7102_, lean_object* v_a_7103_, lean_object* v_a_7104_){
_start:
{
lean_object* v_toGoalState_7106_; lean_object* v_split_7107_; lean_object* v_mvarId_7108_; lean_object* v_candidates_7109_; lean_object* v___f_7110_; lean_object* v___f_7111_; lean_object* v___x_7112_; 
v_toGoalState_7106_ = lean_ctor_get(v_goal_7093_, 0);
v_split_7107_ = lean_ctor_get(v_toGoalState_7106_, 15);
v_mvarId_7108_ = lean_ctor_get(v_goal_7093_, 1);
lean_inc(v_mvarId_7108_);
v_candidates_7109_ = lean_ctor_get(v_split_7107_, 0);
lean_inc(v_candidates_7109_);
v___f_7110_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_7111_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_7111_, 0, v_goal_7093_);
v___x_7112_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_7108_, v___f_7111_, v_a_7096_, v_a_7097_, v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_);
if (lean_obj_tag(v___x_7112_) == 0)
{
lean_object* v_a_7113_; lean_object* v_fst_7114_; 
v_a_7113_ = lean_ctor_get(v___x_7112_, 0);
lean_inc(v_a_7113_);
lean_dec_ref_known(v___x_7112_, 1);
v_fst_7114_ = lean_ctor_get(v_a_7113_, 0);
if (lean_obj_tag(v_fst_7114_) == 1)
{
lean_object* v_snd_7115_; lean_object* v_c_7116_; lean_object* v_numCases_7117_; uint8_t v_isRec_7118_; lean_object* v___y_7120_; lean_object* v___x_7128_; lean_object* v___x_7129_; lean_object* v___x_7130_; uint8_t v___x_7133_; 
lean_inc_ref(v_fst_7114_);
v_snd_7115_ = lean_ctor_get(v_a_7113_, 1);
lean_inc(v_snd_7115_);
lean_dec(v_a_7113_);
v_c_7116_ = lean_ctor_get(v_fst_7114_, 0);
lean_inc_ref(v_c_7116_);
v_numCases_7117_ = lean_ctor_get(v_fst_7114_, 1);
lean_inc(v_numCases_7117_);
v_isRec_7118_ = lean_ctor_get_uint8(v_fst_7114_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_7114_, 2);
v___x_7128_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_7116_);
v___x_7129_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_7115_, v___x_7128_);
lean_dec_ref(v___x_7128_);
v___x_7130_ = lean_unsigned_to_nat(1u);
v___x_7133_ = lean_nat_dec_lt(v___x_7130_, v_numCases_7117_);
if (v___x_7133_ == 0)
{
if (v_isRec_7118_ == 0)
{
v___y_7120_ = v___x_7129_;
goto v___jp_7119_;
}
else
{
goto v___jp_7131_;
}
}
else
{
goto v___jp_7131_;
}
v___jp_7119_:
{
lean_object* v___f_7121_; lean_object* v___x_7122_; lean_object* v___x_7123_; lean_object* v___x_7124_; lean_object* v___x_7125_; lean_object* v___x_7126_; lean_object* v___x_7127_; 
v___f_7121_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_7121_, 0, v___y_7120_);
lean_closure_set(v___f_7121_, 1, v___f_7110_);
v___x_7122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7122_, 0, v_candidates_7109_);
v___x_7123_ = lean_box(v_isRec_7118_);
v___x_7124_ = lean_box(v_stopAtFirstFailure_7091_);
v___x_7125_ = lean_box(v_compress_7092_);
v___x_7126_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_7126_, 0, v_c_7116_);
lean_closure_set(v___x_7126_, 1, v_numCases_7117_);
lean_closure_set(v___x_7126_, 2, v___x_7123_);
lean_closure_set(v___x_7126_, 3, v___x_7124_);
lean_closure_set(v___x_7126_, 4, v___x_7125_);
lean_closure_set(v___x_7126_, 5, v___x_7122_);
v___x_7127_ = l_Lean_Meta_Grind_Action_andThen(v___x_7126_, v___f_7121_, v_snd_7115_, v_kna_7094_, v_kp_7095_, v_a_7096_, v_a_7097_, v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_);
return v___x_7127_;
}
v___jp_7131_:
{
lean_object* v___x_7132_; 
v___x_7132_ = lean_nat_add(v___x_7129_, v___x_7130_);
lean_dec(v___x_7129_);
v___y_7120_ = v___x_7132_;
goto v___jp_7119_;
}
}
else
{
lean_object* v_snd_7134_; lean_object* v___x_7135_; 
lean_dec(v_candidates_7109_);
lean_dec_ref(v_kp_7095_);
v_snd_7134_ = lean_ctor_get(v_a_7113_, 1);
lean_inc(v_snd_7134_);
lean_dec(v_a_7113_);
lean_inc(v_a_7104_);
lean_inc_ref(v_a_7103_);
lean_inc(v_a_7102_);
lean_inc_ref(v_a_7101_);
lean_inc(v_a_7100_);
lean_inc_ref(v_a_7099_);
lean_inc(v_a_7098_);
lean_inc_ref(v_a_7097_);
lean_inc(v_a_7096_);
v___x_7135_ = lean_apply_11(v_kna_7094_, v_snd_7134_, v_a_7096_, v_a_7097_, v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, lean_box(0));
return v___x_7135_;
}
}
else
{
lean_object* v_a_7136_; lean_object* v___x_7138_; uint8_t v_isShared_7139_; uint8_t v_isSharedCheck_7143_; 
lean_dec(v_candidates_7109_);
lean_dec_ref(v_kp_7095_);
lean_dec_ref(v_kna_7094_);
v_a_7136_ = lean_ctor_get(v___x_7112_, 0);
v_isSharedCheck_7143_ = !lean_is_exclusive(v___x_7112_);
if (v_isSharedCheck_7143_ == 0)
{
v___x_7138_ = v___x_7112_;
v_isShared_7139_ = v_isSharedCheck_7143_;
goto v_resetjp_7137_;
}
else
{
lean_inc(v_a_7136_);
lean_dec(v___x_7112_);
v___x_7138_ = lean_box(0);
v_isShared_7139_ = v_isSharedCheck_7143_;
goto v_resetjp_7137_;
}
v_resetjp_7137_:
{
lean_object* v___x_7141_; 
if (v_isShared_7139_ == 0)
{
v___x_7141_ = v___x_7138_;
goto v_reusejp_7140_;
}
else
{
lean_object* v_reuseFailAlloc_7142_; 
v_reuseFailAlloc_7142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7142_, 0, v_a_7136_);
v___x_7141_ = v_reuseFailAlloc_7142_;
goto v_reusejp_7140_;
}
v_reusejp_7140_:
{
return v___x_7141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_7144_, lean_object* v_compress_7145_, lean_object* v_goal_7146_, lean_object* v_kna_7147_, lean_object* v_kp_7148_, lean_object* v_a_7149_, lean_object* v_a_7150_, lean_object* v_a_7151_, lean_object* v_a_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_, lean_object* v_a_7155_, lean_object* v_a_7156_, lean_object* v_a_7157_, lean_object* v_a_7158_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_7159_; uint8_t v_compress_boxed_7160_; lean_object* v_res_7161_; 
v_stopAtFirstFailure_boxed_7159_ = lean_unbox(v_stopAtFirstFailure_7144_);
v_compress_boxed_7160_ = lean_unbox(v_compress_7145_);
v_res_7161_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_7159_, v_compress_boxed_7160_, v_goal_7146_, v_kna_7147_, v_kp_7148_, v_a_7149_, v_a_7150_, v_a_7151_, v_a_7152_, v_a_7153_, v_a_7154_, v_a_7155_, v_a_7156_, v_a_7157_);
lean_dec(v_a_7157_);
lean_dec_ref(v_a_7156_);
lean_dec(v_a_7155_);
lean_dec_ref(v_a_7154_);
lean_dec(v_a_7153_);
lean_dec_ref(v_a_7152_);
lean_dec(v_a_7151_);
lean_dec_ref(v_a_7150_);
lean_dec(v_a_7149_);
return v_res_7161_;
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
