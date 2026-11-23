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
v___x_1599_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkEMStatus___redArg(v___x_1598_, v___y_1592_, v___y_1593_, v___y_1589_, v___y_1588_, v___y_1591_, v___y_1590_);
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
v___y_1590_ = v___y_1716_;
v___y_1591_ = v___y_1715_;
v___y_1592_ = v___y_1707_;
v___y_1593_ = v___y_1711_;
goto v___jp_1587_;
}
}
else
{
v___y_1588_ = v___y_1714_;
v___y_1589_ = v___y_1713_;
v___y_1590_ = v___y_1716_;
v___y_1591_ = v___y_1715_;
v___y_1592_ = v___y_1707_;
v___y_1593_ = v___y_1711_;
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
uint8_t v_a_34316__boxed_2170_; uint8_t v___x_34317__boxed_2171_; lean_object* v_res_2172_; 
v_a_34316__boxed_2170_ = lean_unbox(v_a_2153_);
v___x_34317__boxed_2171_ = lean_unbox(v___x_2154_);
v_res_2172_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34316__boxed_2170_, v___x_34317__boxed_2171_, v_fst_2155_, v_snd_2156_, v___x_2157_, v_____r_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
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
uint8_t v_a_34490__boxed_2418_; lean_object* v_res_2419_; 
v_a_34490__boxed_2418_ = lean_unbox(v_a_2401_);
v_res_2419_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34490__boxed_2418_, v___y_2402_, v_eq_2403_, v_a_2404_, v_b_2405_, v_a_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
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
uint8_t v_a_34971__boxed_2560_; lean_object* v_res_2561_; 
v_a_34971__boxed_2560_ = lean_unbox(v_a_2542_);
v_res_2561_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34971__boxed_2560_, v___y_2543_, v_eq_2544_, v_a_2545_, v_b_2546_, v_inst_2547_, v_a_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
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
lean_object* v___x_2909_; lean_object* v_toGoalState_2910_; lean_object* v_split_2911_; lean_object* v_mvarId_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3029_; 
v___x_2909_ = lean_st_ref_take(v_a_2898_);
v_toGoalState_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc_ref(v_toGoalState_2910_);
v_split_2911_ = lean_ctor_get(v_toGoalState_2910_, 15);
lean_inc_ref(v_split_2911_);
v_mvarId_2912_ = lean_ctor_get(v___x_2909_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v___x_2909_, 0);
lean_dec(v_unused_3030_);
v___x_2914_ = v___x_2909_;
v_isShared_2915_ = v_isSharedCheck_3029_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_mvarId_2912_);
lean_dec(v___x_2909_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3029_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v_nextDeclIdx_2916_; lean_object* v_enodeMap_2917_; lean_object* v_exprs_2918_; lean_object* v_parents_2919_; lean_object* v_congrTable_2920_; lean_object* v_appMap_2921_; lean_object* v_indicesFound_2922_; lean_object* v_toProcess_2923_; lean_object* v_internalizing_2924_; uint8_t v_inconsistent_2925_; lean_object* v_nextIdx_2926_; lean_object* v_newRawFacts_2927_; lean_object* v_facts_2928_; lean_object* v_extThms_2929_; lean_object* v_ematch_2930_; lean_object* v_inj_2931_; lean_object* v_clean_2932_; lean_object* v_sstates_2933_; lean_object* v_goalStack_2934_; uint64_t v_introBase_2935_; lean_object* v_numIntros_2936_; lean_object* v_relevance_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3027_; 
v_nextDeclIdx_2916_ = lean_ctor_get(v_toGoalState_2910_, 0);
v_enodeMap_2917_ = lean_ctor_get(v_toGoalState_2910_, 1);
v_exprs_2918_ = lean_ctor_get(v_toGoalState_2910_, 2);
v_parents_2919_ = lean_ctor_get(v_toGoalState_2910_, 3);
v_congrTable_2920_ = lean_ctor_get(v_toGoalState_2910_, 4);
v_appMap_2921_ = lean_ctor_get(v_toGoalState_2910_, 5);
v_indicesFound_2922_ = lean_ctor_get(v_toGoalState_2910_, 6);
v_toProcess_2923_ = lean_ctor_get(v_toGoalState_2910_, 7);
v_internalizing_2924_ = lean_ctor_get(v_toGoalState_2910_, 8);
v_inconsistent_2925_ = lean_ctor_get_uint8(v_toGoalState_2910_, sizeof(void*)*21 + 8);
v_nextIdx_2926_ = lean_ctor_get(v_toGoalState_2910_, 9);
v_newRawFacts_2927_ = lean_ctor_get(v_toGoalState_2910_, 10);
v_facts_2928_ = lean_ctor_get(v_toGoalState_2910_, 11);
v_extThms_2929_ = lean_ctor_get(v_toGoalState_2910_, 12);
v_ematch_2930_ = lean_ctor_get(v_toGoalState_2910_, 13);
v_inj_2931_ = lean_ctor_get(v_toGoalState_2910_, 14);
v_clean_2932_ = lean_ctor_get(v_toGoalState_2910_, 16);
v_sstates_2933_ = lean_ctor_get(v_toGoalState_2910_, 17);
v_goalStack_2934_ = lean_ctor_get(v_toGoalState_2910_, 18);
v_introBase_2935_ = lean_ctor_get_uint64(v_toGoalState_2910_, sizeof(void*)*21);
v_numIntros_2936_ = lean_ctor_get(v_toGoalState_2910_, 19);
v_relevance_2937_ = lean_ctor_get(v_toGoalState_2910_, 20);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_toGoalState_2910_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v_toGoalState_2910_, 15);
lean_dec(v_unused_3028_);
v___x_2939_ = v_toGoalState_2910_;
v_isShared_2940_ = v_isSharedCheck_3027_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_relevance_2937_);
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
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3027_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_added_2941_; lean_object* v_resolved_2942_; lean_object* v_trace_2943_; lean_object* v_lookaheads_2944_; lean_object* v_argPosMap_2945_; lean_object* v_argsAt_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3025_; 
v_added_2941_ = lean_ctor_get(v_split_2911_, 1);
v_resolved_2942_ = lean_ctor_get(v_split_2911_, 2);
v_trace_2943_ = lean_ctor_get(v_split_2911_, 3);
v_lookaheads_2944_ = lean_ctor_get(v_split_2911_, 4);
v_argPosMap_2945_ = lean_ctor_get(v_split_2911_, 5);
v_argsAt_2946_ = lean_ctor_get(v_split_2911_, 6);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_split_2911_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_split_2911_, 0);
lean_dec(v_unused_3026_);
v___x_2948_ = v_split_2911_;
v_isShared_2949_ = v_isSharedCheck_3025_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_argsAt_2946_);
lean_inc(v_argPosMap_2945_);
lean_inc(v_lookaheads_2944_);
lean_inc(v_trace_2943_);
lean_inc(v_resolved_2942_);
lean_inc(v_added_2941_);
lean_dec(v_split_2911_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3025_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = l_List_reverse___redArg(v_cs_x27_2897_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2950_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_added_2941_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_resolved_2942_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_trace_2943_);
lean_ctor_set(v_reuseFailAlloc_3024_, 4, v_lookaheads_2944_);
lean_ctor_set(v_reuseFailAlloc_3024_, 5, v_argPosMap_2945_);
lean_ctor_set(v_reuseFailAlloc_3024_, 6, v_argsAt_2946_);
v___x_2952_ = v_reuseFailAlloc_3024_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2954_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 15, v___x_2952_);
v___x_2954_ = v___x_2939_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_nextDeclIdx_2916_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_enodeMap_2917_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_exprs_2918_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_parents_2919_);
lean_ctor_set(v_reuseFailAlloc_3023_, 4, v_congrTable_2920_);
lean_ctor_set(v_reuseFailAlloc_3023_, 5, v_appMap_2921_);
lean_ctor_set(v_reuseFailAlloc_3023_, 6, v_indicesFound_2922_);
lean_ctor_set(v_reuseFailAlloc_3023_, 7, v_toProcess_2923_);
lean_ctor_set(v_reuseFailAlloc_3023_, 8, v_internalizing_2924_);
lean_ctor_set(v_reuseFailAlloc_3023_, 9, v_nextIdx_2926_);
lean_ctor_set(v_reuseFailAlloc_3023_, 10, v_newRawFacts_2927_);
lean_ctor_set(v_reuseFailAlloc_3023_, 11, v_facts_2928_);
lean_ctor_set(v_reuseFailAlloc_3023_, 12, v_extThms_2929_);
lean_ctor_set(v_reuseFailAlloc_3023_, 13, v_ematch_2930_);
lean_ctor_set(v_reuseFailAlloc_3023_, 14, v_inj_2931_);
lean_ctor_set(v_reuseFailAlloc_3023_, 15, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_3023_, 16, v_clean_2932_);
lean_ctor_set(v_reuseFailAlloc_3023_, 17, v_sstates_2933_);
lean_ctor_set(v_reuseFailAlloc_3023_, 18, v_goalStack_2934_);
lean_ctor_set(v_reuseFailAlloc_3023_, 19, v_numIntros_2936_);
lean_ctor_set(v_reuseFailAlloc_3023_, 20, v_relevance_2937_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*21 + 8, v_inconsistent_2925_);
lean_ctor_set_uint64(v_reuseFailAlloc_3023_, sizeof(void*)*21, v_introBase_2935_);
v___x_2954_ = v_reuseFailAlloc_3023_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2954_);
v___x_2956_ = v___x_2914_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_mvarId_2912_);
v___x_2956_ = v_reuseFailAlloc_3022_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_st_ref_put(v_a_2898_, v___x_2956_);
if (lean_obj_tag(v_c_x3f_2896_) == 1)
{
lean_object* v___x_2958_; lean_object* v_toGoalState_2959_; lean_object* v_ematch_2960_; lean_object* v_mvarId_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3019_; 
v___x_2958_ = lean_st_ref_take(v_a_2898_);
v_toGoalState_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc_ref(v_toGoalState_2959_);
v_ematch_2960_ = lean_ctor_get(v_toGoalState_2959_, 13);
lean_inc_ref(v_ematch_2960_);
v_mvarId_2961_ = lean_ctor_get(v___x_2958_, 1);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v___x_2958_, 0);
lean_dec(v_unused_3020_);
v___x_2963_ = v___x_2958_;
v_isShared_2964_ = v_isSharedCheck_3019_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_mvarId_2961_);
lean_dec(v___x_2958_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3019_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_nextDeclIdx_2965_; lean_object* v_enodeMap_2966_; lean_object* v_exprs_2967_; lean_object* v_parents_2968_; lean_object* v_congrTable_2969_; lean_object* v_appMap_2970_; lean_object* v_indicesFound_2971_; lean_object* v_toProcess_2972_; lean_object* v_internalizing_2973_; uint8_t v_inconsistent_2974_; lean_object* v_nextIdx_2975_; lean_object* v_newRawFacts_2976_; lean_object* v_facts_2977_; lean_object* v_extThms_2978_; lean_object* v_inj_2979_; lean_object* v_split_2980_; lean_object* v_clean_2981_; lean_object* v_sstates_2982_; lean_object* v_goalStack_2983_; uint64_t v_introBase_2984_; lean_object* v_numIntros_2985_; lean_object* v_relevance_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3017_; 
v_nextDeclIdx_2965_ = lean_ctor_get(v_toGoalState_2959_, 0);
v_enodeMap_2966_ = lean_ctor_get(v_toGoalState_2959_, 1);
v_exprs_2967_ = lean_ctor_get(v_toGoalState_2959_, 2);
v_parents_2968_ = lean_ctor_get(v_toGoalState_2959_, 3);
v_congrTable_2969_ = lean_ctor_get(v_toGoalState_2959_, 4);
v_appMap_2970_ = lean_ctor_get(v_toGoalState_2959_, 5);
v_indicesFound_2971_ = lean_ctor_get(v_toGoalState_2959_, 6);
v_toProcess_2972_ = lean_ctor_get(v_toGoalState_2959_, 7);
v_internalizing_2973_ = lean_ctor_get(v_toGoalState_2959_, 8);
v_inconsistent_2974_ = lean_ctor_get_uint8(v_toGoalState_2959_, sizeof(void*)*21 + 8);
v_nextIdx_2975_ = lean_ctor_get(v_toGoalState_2959_, 9);
v_newRawFacts_2976_ = lean_ctor_get(v_toGoalState_2959_, 10);
v_facts_2977_ = lean_ctor_get(v_toGoalState_2959_, 11);
v_extThms_2978_ = lean_ctor_get(v_toGoalState_2959_, 12);
v_inj_2979_ = lean_ctor_get(v_toGoalState_2959_, 14);
v_split_2980_ = lean_ctor_get(v_toGoalState_2959_, 15);
v_clean_2981_ = lean_ctor_get(v_toGoalState_2959_, 16);
v_sstates_2982_ = lean_ctor_get(v_toGoalState_2959_, 17);
v_goalStack_2983_ = lean_ctor_get(v_toGoalState_2959_, 18);
v_introBase_2984_ = lean_ctor_get_uint64(v_toGoalState_2959_, sizeof(void*)*21);
v_numIntros_2985_ = lean_ctor_get(v_toGoalState_2959_, 19);
v_relevance_2986_ = lean_ctor_get(v_toGoalState_2959_, 20);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_toGoalState_2959_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v_toGoalState_2959_, 13);
lean_dec(v_unused_3018_);
v___x_2988_ = v_toGoalState_2959_;
v_isShared_2989_ = v_isSharedCheck_3017_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_relevance_2986_);
lean_inc(v_numIntros_2985_);
lean_inc(v_goalStack_2983_);
lean_inc(v_sstates_2982_);
lean_inc(v_clean_2981_);
lean_inc(v_split_2980_);
lean_inc(v_inj_2979_);
lean_inc(v_extThms_2978_);
lean_inc(v_facts_2977_);
lean_inc(v_newRawFacts_2976_);
lean_inc(v_nextIdx_2975_);
lean_inc(v_internalizing_2973_);
lean_inc(v_toProcess_2972_);
lean_inc(v_indicesFound_2971_);
lean_inc(v_appMap_2970_);
lean_inc(v_congrTable_2969_);
lean_inc(v_parents_2968_);
lean_inc(v_exprs_2967_);
lean_inc(v_enodeMap_2966_);
lean_inc(v_nextDeclIdx_2965_);
lean_dec(v_toGoalState_2959_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3017_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_thmMap_2990_; lean_object* v_gmt_2991_; lean_object* v_thms_2992_; lean_object* v_newThms_2993_; lean_object* v_numInstances_2994_; lean_object* v_numDelayedInstances_2995_; lean_object* v_preInstances_2996_; lean_object* v_nextThmIdx_2997_; lean_object* v_matchEqNames_2998_; lean_object* v_delayedThmInsts_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3015_; 
v_thmMap_2990_ = lean_ctor_get(v_ematch_2960_, 0);
v_gmt_2991_ = lean_ctor_get(v_ematch_2960_, 1);
v_thms_2992_ = lean_ctor_get(v_ematch_2960_, 2);
v_newThms_2993_ = lean_ctor_get(v_ematch_2960_, 3);
v_numInstances_2994_ = lean_ctor_get(v_ematch_2960_, 4);
v_numDelayedInstances_2995_ = lean_ctor_get(v_ematch_2960_, 5);
v_preInstances_2996_ = lean_ctor_get(v_ematch_2960_, 7);
v_nextThmIdx_2997_ = lean_ctor_get(v_ematch_2960_, 8);
v_matchEqNames_2998_ = lean_ctor_get(v_ematch_2960_, 9);
v_delayedThmInsts_2999_ = lean_ctor_get(v_ematch_2960_, 10);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_ematch_2960_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v_ematch_2960_, 6);
lean_dec(v_unused_3016_);
v___x_3001_ = v_ematch_2960_;
v_isShared_3002_ = v_isSharedCheck_3015_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_delayedThmInsts_2999_);
lean_inc(v_matchEqNames_2998_);
lean_inc(v_nextThmIdx_2997_);
lean_inc(v_preInstances_2996_);
lean_inc(v_numDelayedInstances_2995_);
lean_inc(v_numInstances_2994_);
lean_inc(v_newThms_2993_);
lean_inc(v_thms_2992_);
lean_inc(v_gmt_2991_);
lean_inc(v_thmMap_2990_);
lean_dec(v_ematch_2960_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3015_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = lean_unsigned_to_nat(0u);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 6, v___x_3003_);
v___x_3005_ = v___x_3001_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_thmMap_2990_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_gmt_2991_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_thms_2992_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_newThms_2993_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v_numInstances_2994_);
lean_ctor_set(v_reuseFailAlloc_3014_, 5, v_numDelayedInstances_2995_);
lean_ctor_set(v_reuseFailAlloc_3014_, 6, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3014_, 7, v_preInstances_2996_);
lean_ctor_set(v_reuseFailAlloc_3014_, 8, v_nextThmIdx_2997_);
lean_ctor_set(v_reuseFailAlloc_3014_, 9, v_matchEqNames_2998_);
lean_ctor_set(v_reuseFailAlloc_3014_, 10, v_delayedThmInsts_2999_);
v___x_3005_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 13, v___x_3005_);
v___x_3007_ = v___x_2988_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_nextDeclIdx_2965_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_enodeMap_2966_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_exprs_2967_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_parents_2968_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_congrTable_2969_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v_appMap_2970_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v_indicesFound_2971_);
lean_ctor_set(v_reuseFailAlloc_3013_, 7, v_toProcess_2972_);
lean_ctor_set(v_reuseFailAlloc_3013_, 8, v_internalizing_2973_);
lean_ctor_set(v_reuseFailAlloc_3013_, 9, v_nextIdx_2975_);
lean_ctor_set(v_reuseFailAlloc_3013_, 10, v_newRawFacts_2976_);
lean_ctor_set(v_reuseFailAlloc_3013_, 11, v_facts_2977_);
lean_ctor_set(v_reuseFailAlloc_3013_, 12, v_extThms_2978_);
lean_ctor_set(v_reuseFailAlloc_3013_, 13, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3013_, 14, v_inj_2979_);
lean_ctor_set(v_reuseFailAlloc_3013_, 15, v_split_2980_);
lean_ctor_set(v_reuseFailAlloc_3013_, 16, v_clean_2981_);
lean_ctor_set(v_reuseFailAlloc_3013_, 17, v_sstates_2982_);
lean_ctor_set(v_reuseFailAlloc_3013_, 18, v_goalStack_2983_);
lean_ctor_set(v_reuseFailAlloc_3013_, 19, v_numIntros_2985_);
lean_ctor_set(v_reuseFailAlloc_3013_, 20, v_relevance_2986_);
lean_ctor_set_uint8(v_reuseFailAlloc_3013_, sizeof(void*)*21 + 8, v_inconsistent_2974_);
lean_ctor_set_uint64(v_reuseFailAlloc_3013_, sizeof(void*)*21, v_introBase_2984_);
v___x_3007_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3009_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_3007_);
v___x_3009_ = v___x_2963_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_mvarId_2961_);
v___x_3009_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_st_ref_put(v_a_2898_, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_c_x3f_2896_);
return v___x_3011_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_c_x3f_2896_);
return v___x_3021_;
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
lean_object* v_head_3031_; lean_object* v_tail_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3252_; 
v_head_3031_ = lean_ctor_get(v_cs_2895_, 0);
v_tail_3032_ = lean_ctor_get(v_cs_2895_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_cs_2895_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3034_ = v_cs_2895_;
v_isShared_3035_ = v_isSharedCheck_3252_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_tail_3032_);
lean_inc(v_head_3031_);
lean_dec(v_cs_2895_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3252_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3052_; uint8_t v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; uint8_t v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; uint8_t v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3108_; uint8_t v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; uint8_t v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; uint8_t v___y_3141_; lean_object* v___x_3144_; 
v___x_3144_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_3031_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; uint8_t v___x_3146_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
if (v___x_3146_ == 0)
{
lean_del_object(v___x_3034_);
lean_dec(v_head_3031_);
v_cs_2895_ = v_tail_3032_;
goto _start;
}
else
{
lean_object* v_toCold_3148_; lean_object* v_options_3149_; lean_object* v_inheritedTraceOptions_3150_; uint8_t v_hasTrace_3151_; uint8_t v___x_3152_; lean_object* v___y_3154_; uint8_t v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; uint8_t v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; uint8_t v___y_3167_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; 
v_toCold_3148_ = lean_ctor_get(v_a_2906_, 0);
v_options_3149_ = lean_ctor_get(v_toCold_3148_, 2);
v_inheritedTraceOptions_3150_ = lean_ctor_get(v_toCold_3148_, 11);
v_hasTrace_3151_ = lean_ctor_get_uint8(v_options_3149_, sizeof(void*)*1);
v___x_3152_ = 0;
if (v_hasTrace_3151_ == 0)
{
v___y_3178_ = v_a_2898_;
v___y_3179_ = v_a_2899_;
v___y_3180_ = v_a_2900_;
v___y_3181_ = v_a_2901_;
v___y_3182_ = v_a_2902_;
v___y_3183_ = v_a_2903_;
v___y_3184_ = v_a_2904_;
v___y_3185_ = v_a_2905_;
v___y_3186_ = v_a_2906_;
v___y_3187_ = v_a_2907_;
goto v___jp_3177_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3221_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3150_, v_options_3149_, v___x_3220_);
if (v___x_3221_ == 0)
{
v___y_3178_ = v_a_2898_;
v___y_3179_ = v_a_2899_;
v___y_3180_ = v_a_2900_;
v___y_3181_ = v_a_2901_;
v___y_3182_ = v_a_2902_;
v___y_3183_ = v_a_2903_;
v___y_3184_ = v_a_2904_;
v___y_3185_ = v_a_2905_;
v___y_3186_ = v_a_2906_;
v___y_3187_ = v_a_2907_;
goto v___jp_3177_;
}
else
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Meta_Grind_updateLastTag(v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec_ref_known(v___x_3222_, 1);
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3224_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_3031_);
v___x_3225_ = l_Lean_MessageData_ofExpr(v___x_3224_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3223_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3219_, v___x_3226_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_dec_ref_known(v___x_3227_, 1);
v___y_3178_ = v_a_2898_;
v___y_3179_ = v_a_2899_;
v___y_3180_ = v_a_2900_;
v___y_3181_ = v_a_2901_;
v___y_3182_ = v_a_2902_;
v___y_3183_ = v_a_2903_;
v___y_3184_ = v_a_2904_;
v___y_3185_ = v_a_2905_;
v___y_3186_ = v_a_2906_;
v___y_3187_ = v_a_2907_;
goto v___jp_3177_;
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3236_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3222_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3222_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
v___jp_3153_:
{
if (lean_obj_tag(v_c_x3f_2896_) == 0)
{
lean_object* v___x_3168_; 
lean_del_object(v___x_3034_);
v___x_3168_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3168_, 0, v_head_3031_);
lean_ctor_set(v___x_3168_, 1, v___y_3158_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*2, v___y_3162_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*2 + 1, v___y_3155_);
v_cs_2895_ = v_tail_3032_;
v_c_x3f_2896_ = v___x_3168_;
v_a_2898_ = v___y_3163_;
v_a_2899_ = v___y_3165_;
v_a_2900_ = v___y_3156_;
v_a_2901_ = v___y_3154_;
v_a_2902_ = v___y_3161_;
v_a_2903_ = v___y_3166_;
v_a_2904_ = v___y_3164_;
v_a_2905_ = v___y_3160_;
v_a_2906_ = v___y_3157_;
v_a_2907_ = v___y_3159_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3170_; 
v_tryPostpone_3170_ = lean_ctor_get_uint8(v_c_x3f_2896_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3170_ == 0)
{
if (v___y_3155_ == 0)
{
lean_object* v_c_3171_; lean_object* v_numCases_3172_; 
v_c_3171_ = lean_ctor_get(v_c_x3f_2896_, 0);
v_numCases_3172_ = lean_ctor_get(v_c_x3f_2896_, 1);
lean_inc_ref(v_c_3171_);
lean_inc(v_numCases_3172_);
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3156_;
v___y_3129_ = v___y_3157_;
v___y_3130_ = v___y_3158_;
v___y_3131_ = v_numCases_3172_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
v___y_3135_ = v___y_3162_;
v___y_3136_ = v_c_3171_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3165_;
v___y_3140_ = v___y_3166_;
v___y_3141_ = v___x_3152_;
goto v___jp_3125_;
}
else
{
lean_dec(v___y_3158_);
v___y_3037_ = v___y_3154_;
v___y_3038_ = v___y_3156_;
v___y_3039_ = v___y_3157_;
v___y_3040_ = v___y_3159_;
v___y_3041_ = v___y_3163_;
v___y_3042_ = v___y_3164_;
v___y_3043_ = v___y_3165_;
v___y_3044_ = v___y_3160_;
v___y_3045_ = v___y_3166_;
v___y_3046_ = v___y_3161_;
goto v___jp_3036_;
}
}
else
{
if (v___y_3155_ == 0)
{
lean_object* v_c_3173_; 
lean_del_object(v___x_3034_);
v_c_3173_ = lean_ctor_get(v_c_x3f_2896_, 0);
lean_inc_ref(v_c_3173_);
lean_dec_ref_known(v_c_x3f_2896_, 2);
v___y_3052_ = v___y_3154_;
v___y_3053_ = v___y_3155_;
v___y_3054_ = v___y_3156_;
v___y_3055_ = v___y_3157_;
v___y_3056_ = v___y_3159_;
v___y_3057_ = v___y_3158_;
v___y_3058_ = v___y_3160_;
v___y_3059_ = v___y_3161_;
v___y_3060_ = v___y_3162_;
v___y_3061_ = v_c_3173_;
v___y_3062_ = v___y_3163_;
v___y_3063_ = v___y_3164_;
v___y_3064_ = v___y_3165_;
v___y_3065_ = v___y_3166_;
goto v___jp_3051_;
}
else
{
if (v___y_3167_ == 0)
{
lean_object* v_c_3174_; lean_object* v_numCases_3175_; 
v_c_3174_ = lean_ctor_get(v_c_x3f_2896_, 0);
v_numCases_3175_ = lean_ctor_get(v_c_x3f_2896_, 1);
lean_inc_ref(v_c_3174_);
lean_inc(v_numCases_3175_);
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3156_;
v___y_3129_ = v___y_3157_;
v___y_3130_ = v___y_3158_;
v___y_3131_ = v_numCases_3175_;
v___y_3132_ = v___y_3159_;
v___y_3133_ = v___y_3160_;
v___y_3134_ = v___y_3161_;
v___y_3135_ = v___y_3162_;
v___y_3136_ = v_c_3174_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3165_;
v___y_3140_ = v___y_3166_;
v___y_3141_ = v___y_3167_;
goto v___jp_3125_;
}
else
{
lean_object* v_c_3176_; 
lean_del_object(v___x_3034_);
v_c_3176_ = lean_ctor_get(v_c_x3f_2896_, 0);
lean_inc_ref(v_c_3176_);
lean_dec_ref_known(v_c_x3f_2896_, 2);
v___y_3052_ = v___y_3154_;
v___y_3053_ = v___y_3155_;
v___y_3054_ = v___y_3156_;
v___y_3055_ = v___y_3157_;
v___y_3056_ = v___y_3159_;
v___y_3057_ = v___y_3158_;
v___y_3058_ = v___y_3160_;
v___y_3059_ = v___y_3161_;
v___y_3060_ = v___y_3162_;
v___y_3061_ = v_c_3176_;
v___y_3062_ = v___y_3163_;
v___y_3063_ = v___y_3164_;
v___y_3064_ = v___y_3165_;
v___y_3065_ = v___y_3166_;
goto v___jp_3051_;
}
}
}
}
}
v___jp_3177_:
{
lean_object* v___x_3188_; 
lean_inc(v_head_3031_);
v___x_3188_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_3031_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
switch(lean_obj_tag(v_a_3189_))
{
case 0:
{
lean_del_object(v___x_3034_);
lean_dec(v_head_3031_);
v_cs_2895_ = v_tail_3032_;
v_a_2898_ = v___y_3178_;
v_a_2899_ = v___y_3179_;
v_a_2900_ = v___y_3180_;
v_a_2901_ = v___y_3181_;
v_a_2902_ = v___y_3182_;
v_a_2903_ = v___y_3183_;
v_a_2904_ = v___y_3184_;
v_a_2905_ = v___y_3185_;
v_a_2906_ = v___y_3186_;
v_a_2907_ = v___y_3187_;
goto _start;
}
case 1:
{
lean_object* v___x_3191_; 
lean_del_object(v___x_3034_);
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_head_3031_);
lean_ctor_set(v___x_3191_, 1, v_cs_x27_2897_);
v_cs_2895_ = v_tail_3032_;
v_cs_x27_2897_ = v___x_3191_;
v_a_2898_ = v___y_3178_;
v_a_2899_ = v___y_3179_;
v_a_2900_ = v___y_3180_;
v_a_2901_ = v___y_3181_;
v_a_2902_ = v___y_3182_;
v_a_2903_ = v___y_3183_;
v_a_2904_ = v___y_3184_;
v_a_2905_ = v___y_3185_;
v_a_2906_ = v___y_3186_;
v_a_2907_ = v___y_3187_;
goto _start;
}
default: 
{
lean_object* v_numCases_3193_; uint8_t v_isRec_3194_; uint8_t v_tryPostpone_3195_; lean_object* v___x_3196_; 
v_numCases_3193_ = lean_ctor_get(v_a_3189_, 0);
lean_inc(v_numCases_3193_);
v_isRec_3194_ = lean_ctor_get_uint8(v_a_3189_, sizeof(void*)*1);
v_tryPostpone_3195_ = lean_ctor_get_uint8(v_a_3189_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3189_, 1);
v___x_3196_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3180_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; uint8_t v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = lean_unbox(v_a_3197_);
lean_dec(v_a_3197_);
if (v___x_3198_ == 0)
{
v___y_3154_ = v___y_3181_;
v___y_3155_ = v_tryPostpone_3195_;
v___y_3156_ = v___y_3180_;
v___y_3157_ = v___y_3186_;
v___y_3158_ = v_numCases_3193_;
v___y_3159_ = v___y_3187_;
v___y_3160_ = v___y_3185_;
v___y_3161_ = v___y_3182_;
v___y_3162_ = v_isRec_3194_;
v___y_3163_ = v___y_3178_;
v___y_3164_ = v___y_3184_;
v___y_3165_ = v___y_3179_;
v___y_3166_ = v___y_3183_;
v___y_3167_ = v___x_3152_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = lean_unsigned_to_nat(1u);
v___x_3200_ = lean_nat_dec_lt(v___x_3199_, v_numCases_3193_);
if (v___x_3200_ == 0)
{
v___y_3154_ = v___y_3181_;
v___y_3155_ = v_tryPostpone_3195_;
v___y_3156_ = v___y_3180_;
v___y_3157_ = v___y_3186_;
v___y_3158_ = v_numCases_3193_;
v___y_3159_ = v___y_3187_;
v___y_3160_ = v___y_3185_;
v___y_3161_ = v___y_3182_;
v___y_3162_ = v_isRec_3194_;
v___y_3163_ = v___y_3178_;
v___y_3164_ = v___y_3184_;
v___y_3165_ = v___y_3179_;
v___y_3166_ = v___y_3183_;
v___y_3167_ = v___x_3200_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3201_; 
lean_dec(v_numCases_3193_);
lean_del_object(v___x_3034_);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_head_3031_);
lean_ctor_set(v___x_3201_, 1, v_cs_x27_2897_);
v_cs_2895_ = v_tail_3032_;
v_cs_x27_2897_ = v___x_3201_;
v_a_2898_ = v___y_3178_;
v_a_2899_ = v___y_3179_;
v_a_2900_ = v___y_3180_;
v_a_2901_ = v___y_3181_;
v_a_2902_ = v___y_3182_;
v_a_2903_ = v___y_3183_;
v_a_2904_ = v___y_3184_;
v_a_2905_ = v___y_3185_;
v_a_2906_ = v___y_3186_;
v_a_2907_ = v___y_3187_;
goto _start;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_numCases_3193_);
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3203_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3196_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3196_);
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
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3211_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3188_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3188_);
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
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3244_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3144_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3144_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
v___jp_3036_:
{
lean_object* v___x_3048_; 
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 1, v_cs_x27_2897_);
v___x_3048_ = v___x_3034_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_head_3031_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_cs_x27_2897_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v_cs_2895_ = v_tail_3032_;
v_cs_x27_2897_ = v___x_3048_;
v_a_2898_ = v___y_3041_;
v_a_2899_ = v___y_3043_;
v_a_2900_ = v___y_3038_;
v_a_2901_ = v___y_3037_;
v_a_2902_ = v___y_3046_;
v_a_2903_ = v___y_3045_;
v_a_2904_ = v___y_3042_;
v_a_2905_ = v___y_3044_;
v_a_2906_ = v___y_3039_;
v_a_2907_ = v___y_3040_;
goto _start;
}
}
v___jp_3051_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3066_, 0, v_head_3031_);
lean_ctor_set(v___x_3066_, 1, v___y_3057_);
lean_ctor_set_uint8(v___x_3066_, sizeof(void*)*2, v___y_3060_);
lean_ctor_set_uint8(v___x_3066_, sizeof(void*)*2 + 1, v___y_3053_);
v___x_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___y_3061_);
lean_ctor_set(v___x_3067_, 1, v_cs_x27_2897_);
v_cs_2895_ = v_tail_3032_;
v_c_x3f_2896_ = v___x_3066_;
v_cs_x27_2897_ = v___x_3067_;
v_a_2898_ = v___y_3062_;
v_a_2899_ = v___y_3064_;
v_a_2900_ = v___y_3054_;
v_a_2901_ = v___y_3052_;
v_a_2902_ = v___y_3059_;
v_a_2903_ = v___y_3065_;
v_a_2904_ = v___y_3063_;
v_a_2905_ = v___y_3058_;
v_a_2906_ = v___y_3055_;
v_a_2907_ = v___y_3056_;
goto _start;
}
v___jp_3069_:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_3031_, v___y_3081_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
v___x_3087_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; uint8_t v___x_3089_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
v___x_3089_ = lean_nat_dec_lt(v_a_3086_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec(v_a_3086_);
if (v___x_3089_ == 0)
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_nat_dec_lt(v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
if (v___x_3090_ == 0)
{
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3074_);
v___y_3037_ = v___y_3070_;
v___y_3038_ = v___y_3072_;
v___y_3039_ = v___y_3073_;
v___y_3040_ = v___y_3076_;
v___y_3041_ = v___y_3081_;
v___y_3042_ = v___y_3082_;
v___y_3043_ = v___y_3083_;
v___y_3044_ = v___y_3077_;
v___y_3045_ = v___y_3084_;
v___y_3046_ = v___y_3078_;
goto v___jp_3036_;
}
else
{
lean_del_object(v___x_3034_);
lean_dec(v_c_x3f_2896_);
v___y_3052_ = v___y_3070_;
v___y_3053_ = v___y_3071_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3073_;
v___y_3056_ = v___y_3076_;
v___y_3057_ = v___y_3074_;
v___y_3058_ = v___y_3077_;
v___y_3059_ = v___y_3078_;
v___y_3060_ = v___y_3079_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3081_;
v___y_3063_ = v___y_3082_;
v___y_3064_ = v___y_3083_;
v___y_3065_ = v___y_3084_;
goto v___jp_3051_;
}
}
else
{
lean_dec(v___y_3075_);
lean_del_object(v___x_3034_);
lean_dec(v_c_x3f_2896_);
v___y_3052_ = v___y_3070_;
v___y_3053_ = v___y_3071_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3073_;
v___y_3056_ = v___y_3076_;
v___y_3057_ = v___y_3074_;
v___y_3058_ = v___y_3077_;
v___y_3059_ = v___y_3078_;
v___y_3060_ = v___y_3079_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3081_;
v___y_3063_ = v___y_3082_;
v___y_3064_ = v___y_3083_;
v___y_3065_ = v___y_3084_;
goto v___jp_3051_;
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_3086_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3075_);
lean_dec(v___y_3074_);
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3091_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3087_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3087_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3075_);
lean_dec(v___y_3074_);
lean_del_object(v___x_3034_);
lean_dec(v_tail_3032_);
lean_dec(v_head_3031_);
lean_dec(v_cs_x27_2897_);
lean_dec(v_c_x3f_2896_);
v_a_3099_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3085_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3085_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
v___jp_3107_:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = lean_unsigned_to_nat(1u);
v___x_3124_ = lean_nat_dec_lt(v___x_3123_, v___y_3112_);
if (v___x_3124_ == 0)
{
v___y_3070_ = v___y_3108_;
v___y_3071_ = v___y_3109_;
v___y_3072_ = v___y_3110_;
v___y_3073_ = v___y_3111_;
v___y_3074_ = v___y_3113_;
v___y_3075_ = v___y_3112_;
v___y_3076_ = v___y_3114_;
v___y_3077_ = v___y_3115_;
v___y_3078_ = v___y_3116_;
v___y_3079_ = v___y_3117_;
v___y_3080_ = v___y_3118_;
v___y_3081_ = v___y_3119_;
v___y_3082_ = v___y_3120_;
v___y_3083_ = v___y_3121_;
v___y_3084_ = v___y_3122_;
goto v___jp_3069_;
}
else
{
lean_dec(v___y_3112_);
lean_del_object(v___x_3034_);
lean_dec(v_c_x3f_2896_);
v___y_3052_ = v___y_3108_;
v___y_3053_ = v___y_3109_;
v___y_3054_ = v___y_3110_;
v___y_3055_ = v___y_3111_;
v___y_3056_ = v___y_3114_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3115_;
v___y_3059_ = v___y_3116_;
v___y_3060_ = v___y_3117_;
v___y_3061_ = v___y_3118_;
v___y_3062_ = v___y_3119_;
v___y_3063_ = v___y_3120_;
v___y_3064_ = v___y_3121_;
v___y_3065_ = v___y_3122_;
goto v___jp_3051_;
}
}
v___jp_3125_:
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = lean_nat_dec_eq(v___y_3130_, v___x_3142_);
if (v___x_3143_ == 0)
{
v___y_3070_ = v___y_3126_;
v___y_3071_ = v___y_3127_;
v___y_3072_ = v___y_3128_;
v___y_3073_ = v___y_3129_;
v___y_3074_ = v___y_3130_;
v___y_3075_ = v___y_3131_;
v___y_3076_ = v___y_3132_;
v___y_3077_ = v___y_3133_;
v___y_3078_ = v___y_3134_;
v___y_3079_ = v___y_3135_;
v___y_3080_ = v___y_3136_;
v___y_3081_ = v___y_3137_;
v___y_3082_ = v___y_3138_;
v___y_3083_ = v___y_3139_;
v___y_3084_ = v___y_3140_;
goto v___jp_3069_;
}
else
{
if (v___y_3135_ == 0)
{
v___y_3108_ = v___y_3126_;
v___y_3109_ = v___y_3127_;
v___y_3110_ = v___y_3128_;
v___y_3111_ = v___y_3129_;
v___y_3112_ = v___y_3131_;
v___y_3113_ = v___y_3130_;
v___y_3114_ = v___y_3132_;
v___y_3115_ = v___y_3133_;
v___y_3116_ = v___y_3134_;
v___y_3117_ = v___y_3135_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3139_;
v___y_3122_ = v___y_3140_;
goto v___jp_3107_;
}
else
{
if (v___y_3141_ == 0)
{
v___y_3070_ = v___y_3126_;
v___y_3071_ = v___y_3127_;
v___y_3072_ = v___y_3128_;
v___y_3073_ = v___y_3129_;
v___y_3074_ = v___y_3130_;
v___y_3075_ = v___y_3131_;
v___y_3076_ = v___y_3132_;
v___y_3077_ = v___y_3133_;
v___y_3078_ = v___y_3134_;
v___y_3079_ = v___y_3135_;
v___y_3080_ = v___y_3136_;
v___y_3081_ = v___y_3137_;
v___y_3082_ = v___y_3138_;
v___y_3083_ = v___y_3139_;
v___y_3084_ = v___y_3140_;
goto v___jp_3069_;
}
else
{
v___y_3108_ = v___y_3126_;
v___y_3109_ = v___y_3127_;
v___y_3110_ = v___y_3128_;
v___y_3111_ = v___y_3129_;
v___y_3112_ = v___y_3131_;
v___y_3113_ = v___y_3130_;
v___y_3114_ = v___y_3132_;
v___y_3115_ = v___y_3133_;
v___y_3116_ = v___y_3134_;
v___y_3117_ = v___y_3135_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3139_;
v___y_3122_ = v___y_3140_;
goto v___jp_3107_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3253_, lean_object* v_c_x3f_3254_, lean_object* v_cs_x27_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3253_, v_c_x3f_3254_, v_cs_x27_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec(v_a_3256_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3268_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3315_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3315_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3315_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_unbox(v_a_3280_);
lean_dec(v_a_3280_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; 
lean_del_object(v___x_3282_);
v___x_3285_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3270_, v_a_3271_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3302_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3302_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3302_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
uint8_t v___x_3290_; 
v___x_3290_ = lean_unbox(v_a_3286_);
lean_dec(v_a_3286_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v_toGoalState_3292_; lean_object* v_split_3293_; lean_object* v_candidates_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_del_object(v___x_3288_);
v___x_3291_ = lean_st_ref_get(v_a_3268_);
v_toGoalState_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc_ref(v_toGoalState_3292_);
lean_dec(v___x_3291_);
v_split_3293_ = lean_ctor_get(v_toGoalState_3292_, 15);
lean_inc_ref(v_split_3293_);
lean_dec_ref(v_toGoalState_3292_);
v_candidates_3294_ = lean_ctor_get(v_split_3293_, 0);
lean_inc(v_candidates_3294_);
lean_dec_ref(v_split_3293_);
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_box(0);
v___x_3297_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3294_, v___x_3295_, v___x_3296_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
return v___x_3297_;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3298_ = lean_box(0);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3298_);
v___x_3300_ = v___x_3288_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
v_a_3303_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3285_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3285_);
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
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_box(0);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3311_);
v___x_3313_ = v___x_3282_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
v_a_3316_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3279_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3279_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec(v_a_3324_);
return v_res_3335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_box(0);
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3345_ = l_Lean_mkConst(v___x_3344_, v___x_3343_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3346_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3348_ = l_Lean_Expr_app___override(v___x_3347_, v_c_3346_);
return v___x_3348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_box(0);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3356_ = l_Lean_mkConst(v___x_3355_, v___x_3354_);
return v___x_3356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = lean_box(0);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4));
v___x_3364_ = l_Lean_mkConst(v___x_3363_, v___x_3362_);
return v___x_3364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = lean_box(0);
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7));
v___x_3372_ = l_Lean_mkConst(v___x_3371_, v___x_3370_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___x_3434_; 
lean_inc_ref(v_c_3373_);
v___x_3434_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3373_, v_a_3381_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3507_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3507_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3507_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = l_Lean_Expr_cleanupAnnotations(v_a_3435_);
lean_dec(v_a_3435_);
v___x_3440_ = l_Lean_Expr_isApp(v___x_3439_);
if (v___x_3440_ == 0)
{
lean_dec_ref(v___x_3439_);
lean_del_object(v___x_3437_);
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
v___y_3402_ = v_a_3382_;
v___y_3403_ = v_a_3383_;
goto v___jp_3393_;
}
else
{
lean_object* v_arg_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v_arg_3441_ = lean_ctor_get(v___x_3439_, 1);
lean_inc_ref(v_arg_3441_);
v___x_3442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3439_);
lean_dec_ref(v___x_3439_);
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3444_ = l_Lean_Expr_isConstOf(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
uint8_t v___x_3445_; 
v___x_3445_ = l_Lean_Expr_isApp(v___x_3442_);
if (v___x_3445_ == 0)
{
lean_dec_ref(v___x_3442_);
lean_dec_ref(v_arg_3441_);
lean_del_object(v___x_3437_);
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
v___y_3402_ = v_a_3382_;
v___y_3403_ = v_a_3383_;
goto v___jp_3393_;
}
else
{
lean_object* v_arg_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_arg_3446_ = lean_ctor_get(v___x_3442_, 1);
lean_inc_ref(v_arg_3446_);
v___x_3447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3442_);
lean_dec_ref(v___x_3442_);
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_3449_ = l_Lean_Expr_isConstOf(v___x_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
uint8_t v___x_3450_; 
v___x_3450_ = l_Lean_Expr_isApp(v___x_3447_);
if (v___x_3450_ == 0)
{
lean_dec_ref(v___x_3447_);
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
lean_del_object(v___x_3437_);
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
v___y_3402_ = v_a_3382_;
v___y_3403_ = v_a_3383_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3447_);
lean_dec_ref(v___x_3447_);
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__20));
v___x_3453_ = l_Lean_Expr_isConstOf(v___x_3451_, v___x_3452_);
lean_dec_ref(v___x_3451_);
if (v___x_3453_ == 0)
{
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
lean_del_object(v___x_3437_);
v___y_3394_ = v_a_3374_;
v___y_3395_ = v_a_3375_;
v___y_3396_ = v_a_3376_;
v___y_3397_ = v_a_3377_;
v___y_3398_ = v_a_3378_;
v___y_3399_ = v_a_3379_;
v___y_3400_ = v_a_3380_;
v___y_3401_ = v_a_3381_;
v___y_3402_ = v_a_3382_;
v___y_3403_ = v_a_3383_;
goto v___jp_3393_;
}
else
{
uint8_t v___x_3454_; 
v___x_3454_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3373_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3373_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3455_);
v___x_3457_ = v___x_3437_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v___x_3459_; 
lean_del_object(v___x_3437_);
lean_inc_ref(v_c_3373_);
v___x_3459_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3373_, v_a_3374_, v_a_3378_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; uint8_t v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = lean_unbox(v_a_3460_);
lean_dec(v_a_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3472_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3472_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3472_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3467_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2);
v___x_3468_ = l_Lean_mkApp3(v___x_3467_, v_arg_3446_, v_arg_3441_, v_a_3463_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3468_);
v___x_3470_ = v___x_3465_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
else
{
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
return v___x_3462_;
}
}
else
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3483_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3483_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3483_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5);
v___x_3479_ = l_Lean_mkApp3(v___x_3478_, v_arg_3446_, v_arg_3441_, v_a_3474_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3479_);
v___x_3481_ = v___x_3476_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
else
{
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
return v___x_3473_;
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
lean_dec_ref(v_c_3373_);
v_a_3484_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3459_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3459_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3492_; 
lean_dec_ref(v___x_3447_);
lean_del_object(v___x_3437_);
v___x_3492_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3502_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3502_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3502_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8);
v___x_3498_ = l_Lean_mkApp3(v___x_3497_, v_arg_3446_, v_arg_3441_, v_a_3493_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3498_);
v___x_3500_ = v___x_3495_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_dec_ref(v_arg_3446_);
lean_dec_ref(v_arg_3441_);
return v___x_3492_;
}
}
}
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_dec_ref(v___x_3442_);
lean_dec_ref(v_c_3373_);
v___x_3503_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3441_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3503_);
v___x_3505_ = v___x_3437_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3373_);
return v___x_3434_;
}
v___jp_3385_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3386_ = lean_unsigned_to_nat(1u);
v___x_3387_ = l_Lean_Expr_getAppNumArgs(v_c_3373_);
v___x_3388_ = lean_nat_sub(v___x_3387_, v___x_3386_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_nat_sub(v___x_3388_, v___x_3386_);
lean_dec(v___x_3388_);
v___x_3390_ = l_Lean_Expr_getRevArg_x21(v_c_3373_, v___x_3389_);
lean_dec_ref(v_c_3373_);
v___x_3391_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3390_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
v___jp_3393_:
{
uint8_t v___x_3404_; 
v___x_3404_ = l_Lean_Meta_Grind_isIte(v_c_3373_);
if (v___x_3404_ == 0)
{
uint8_t v___x_3405_; 
v___x_3405_ = l_Lean_Meta_Grind_isDIte(v_c_3373_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_inc_ref(v_c_3373_);
v___x_3406_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3373_, v___y_3394_, v___y_3398_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3425_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3425_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3425_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_unbox(v_a_3407_);
lean_dec(v_a_3407_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3413_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_c_3373_);
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_c_3373_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
else
{
lean_object* v___x_3415_; 
lean_del_object(v___x_3409_);
lean_inc_ref(v_c_3373_);
v___x_3415_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3373_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3373_, v_a_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_dec_ref(v_c_3373_);
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v_c_3373_);
v_a_3426_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3406_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3406_);
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
}
else
{
goto v___jp_3385_;
}
}
else
{
goto v___jp_3385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec(v_a_3509_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3521_, lean_object* v_major_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3523_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; uint8_t v_trace_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v_trace_3532_ = lean_ctor_get_uint8(v_a_3531_, sizeof(void*)*18);
lean_dec(v_a_3531_);
if (v_trace_3532_ == 0)
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_Meta_Grind_cases(v_mvarId_3521_, v_major_3522_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
return v___x_3533_;
}
else
{
lean_object* v___x_3534_; 
lean_inc(v_a_3528_);
lean_inc_ref(v_a_3527_);
lean_inc(v_a_3526_);
lean_inc_ref(v_a_3525_);
lean_inc_ref(v_major_3522_);
v___x_3534_ = lean_infer_type(v_major_3522_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = l_Lean_Meta_whnfD(v_a_3535_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = l_Lean_Expr_getAppFn(v_a_3537_);
lean_dec(v_a_3537_);
if (lean_obj_tag(v___x_3538_) == 4)
{
lean_object* v_declName_3539_; lean_object* v___x_3540_; 
v_declName_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_declName_3539_);
lean_dec_ref_known(v___x_3538_, 2);
v___x_3540_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3539_, v_a_3524_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3541_; 
lean_dec_ref_known(v___x_3540_, 1);
v___x_3541_ = l_Lean_Meta_Grind_cases(v_mvarId_3521_, v_major_3522_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
return v___x_3541_;
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec_ref(v_major_3522_);
lean_dec(v_mvarId_3521_);
v_a_3542_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3540_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3540_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_object* v___x_3550_; 
lean_dec_ref(v___x_3538_);
v___x_3550_ = l_Lean_Meta_Grind_cases(v_mvarId_3521_, v_major_3522_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
return v___x_3550_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_major_3522_);
lean_dec(v_mvarId_3521_);
v_a_3551_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3536_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3536_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v_major_3522_);
lean_dec(v_mvarId_3521_);
v_a_3559_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3534_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3534_);
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
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref(v_major_3522_);
lean_dec(v_mvarId_3521_);
v_a_3567_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3530_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3530_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3575_, lean_object* v_major_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3575_, v_major_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3585_, lean_object* v_major_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3585_, v_major_3586_, v_a_3589_, v_a_3590_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3599_, lean_object* v_major_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3599_, v_major_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec(v_a_3601_);
return v_res_3612_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3613_){
_start:
{
uint64_t v_anchor_3614_; 
v_anchor_3614_ = lean_ctor_get_uint64(v_e_3613_, sizeof(void*)*3);
return v_anchor_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3615_){
_start:
{
uint64_t v_res_3616_; lean_object* v_r_3617_; 
v_res_3616_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3615_);
lean_dec_ref(v_e_3615_);
v_r_3617_ = lean_box_uint64(v_res_3616_);
return v_r_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3620_, lean_object* v_x_3621_){
_start:
{
if (lean_obj_tag(v_x_3621_) == 0)
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_box(0);
return v___x_3622_;
}
else
{
lean_object* v_key_3623_; lean_object* v_value_3624_; lean_object* v_tail_3625_; uint64_t v___x_3626_; uint8_t v___x_3627_; 
v_key_3623_ = lean_ctor_get(v_x_3621_, 0);
v_value_3624_ = lean_ctor_get(v_x_3621_, 1);
v_tail_3625_ = lean_ctor_get(v_x_3621_, 2);
v___x_3626_ = lean_unbox_uint64(v_key_3623_);
v___x_3627_ = lean_uint64_dec_eq(v___x_3626_, v_a_3620_);
if (v___x_3627_ == 0)
{
v_x_3621_ = v_tail_3625_;
goto _start;
}
else
{
lean_object* v___x_3629_; 
lean_inc(v_value_3624_);
v___x_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3629_, 0, v_value_3624_);
return v___x_3629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3630_, lean_object* v_x_3631_){
_start:
{
uint64_t v_a_boxed_3632_; lean_object* v_res_3633_; 
v_a_boxed_3632_ = lean_unbox_uint64(v_a_3630_);
lean_dec_ref(v_a_3630_);
v_res_3633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3632_, v_x_3631_);
lean_dec(v_x_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3634_, uint64_t v_a_3635_){
_start:
{
lean_object* v_buckets_3636_; lean_object* v___x_3637_; uint64_t v___x_3638_; uint64_t v___x_3639_; uint64_t v_fold_3640_; uint64_t v___x_3641_; uint64_t v___x_3642_; uint64_t v___x_3643_; size_t v___x_3644_; size_t v___x_3645_; size_t v___x_3646_; size_t v___x_3647_; size_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v_buckets_3636_ = lean_ctor_get(v_m_3634_, 1);
v___x_3637_ = lean_array_get_size(v_buckets_3636_);
v___x_3638_ = 32ULL;
v___x_3639_ = lean_uint64_shift_right(v_a_3635_, v___x_3638_);
v_fold_3640_ = lean_uint64_xor(v_a_3635_, v___x_3639_);
v___x_3641_ = 16ULL;
v___x_3642_ = lean_uint64_shift_right(v_fold_3640_, v___x_3641_);
v___x_3643_ = lean_uint64_xor(v_fold_3640_, v___x_3642_);
v___x_3644_ = lean_uint64_to_usize(v___x_3643_);
v___x_3645_ = lean_usize_of_nat(v___x_3637_);
v___x_3646_ = ((size_t)1ULL);
v___x_3647_ = lean_usize_sub(v___x_3645_, v___x_3646_);
v___x_3648_ = lean_usize_land(v___x_3644_, v___x_3647_);
v___x_3649_ = lean_array_uget_borrowed(v_buckets_3636_, v___x_3648_);
v___x_3650_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3635_, v___x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3651_, lean_object* v_a_3652_){
_start:
{
uint64_t v_a_boxed_3653_; lean_object* v_res_3654_; 
v_a_boxed_3653_ = lean_unbox_uint64(v_a_3652_);
lean_dec_ref(v_a_3652_);
v_res_3654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3651_, v_a_boxed_3653_);
lean_dec_ref(v_m_3651_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3655_, lean_object* v_x_3656_){
_start:
{
if (lean_obj_tag(v_x_3656_) == 0)
{
return v_x_3655_;
}
else
{
lean_object* v_key_3657_; lean_object* v_value_3658_; lean_object* v_tail_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3683_; 
v_key_3657_ = lean_ctor_get(v_x_3656_, 0);
v_value_3658_ = lean_ctor_get(v_x_3656_, 1);
v_tail_3659_ = lean_ctor_get(v_x_3656_, 2);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3656_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3661_ = v_x_3656_;
v_isShared_3662_ = v_isSharedCheck_3683_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_tail_3659_);
lean_inc(v_value_3658_);
lean_inc(v_key_3657_);
lean_dec(v_x_3656_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3683_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; uint64_t v___x_3664_; uint64_t v___x_3665_; uint64_t v___x_3666_; uint64_t v___x_3667_; uint64_t v_fold_3668_; uint64_t v___x_3669_; uint64_t v___x_3670_; uint64_t v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; size_t v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3663_ = lean_array_get_size(v_x_3655_);
v___x_3664_ = 32ULL;
v___x_3665_ = lean_unbox_uint64(v_key_3657_);
v___x_3666_ = lean_uint64_shift_right(v___x_3665_, v___x_3664_);
v___x_3667_ = lean_unbox_uint64(v_key_3657_);
v_fold_3668_ = lean_uint64_xor(v___x_3667_, v___x_3666_);
v___x_3669_ = 16ULL;
v___x_3670_ = lean_uint64_shift_right(v_fold_3668_, v___x_3669_);
v___x_3671_ = lean_uint64_xor(v_fold_3668_, v___x_3670_);
v___x_3672_ = lean_uint64_to_usize(v___x_3671_);
v___x_3673_ = lean_usize_of_nat(v___x_3663_);
v___x_3674_ = ((size_t)1ULL);
v___x_3675_ = lean_usize_sub(v___x_3673_, v___x_3674_);
v___x_3676_ = lean_usize_land(v___x_3672_, v___x_3675_);
v___x_3677_ = lean_array_uget_borrowed(v_x_3655_, v___x_3676_);
lean_inc(v___x_3677_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 2, v___x_3677_);
v___x_3679_ = v___x_3661_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_key_3657_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_value_3658_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; 
v___x_3680_ = lean_array_uset(v_x_3655_, v___x_3676_, v___x_3679_);
v_x_3655_ = v___x_3680_;
v_x_3656_ = v_tail_3659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3684_, lean_object* v_source_3685_, lean_object* v_target_3686_){
_start:
{
lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = lean_array_get_size(v_source_3685_);
v___x_3688_ = lean_nat_dec_lt(v_i_3684_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_dec_ref(v_source_3685_);
lean_dec(v_i_3684_);
return v_target_3686_;
}
else
{
lean_object* v_es_3689_; lean_object* v___x_3690_; lean_object* v_source_3691_; lean_object* v_target_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_es_3689_ = lean_array_fget(v_source_3685_, v_i_3684_);
v___x_3690_ = lean_box(0);
v_source_3691_ = lean_array_fset(v_source_3685_, v_i_3684_, v___x_3690_);
v_target_3692_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3686_, v_es_3689_);
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_add(v_i_3684_, v___x_3693_);
lean_dec(v_i_3684_);
v_i_3684_ = v___x_3694_;
v_source_3685_ = v_source_3691_;
v_target_3686_ = v_target_3692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v_nbuckets_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3697_ = lean_array_get_size(v_data_3696_);
v___x_3698_ = lean_unsigned_to_nat(2u);
v_nbuckets_3699_ = lean_nat_mul(v___x_3697_, v___x_3698_);
v___x_3700_ = lean_unsigned_to_nat(0u);
v___x_3701_ = lean_box(0);
v___x_3702_ = lean_mk_array(v_nbuckets_3699_, v___x_3701_);
v___x_3703_ = lean_array_propagate_mark(v_data_3696_, v___x_3702_);
v___x_3704_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3700_, v_data_3696_, v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3705_, lean_object* v_b_3706_, lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 0)
{
lean_dec(v_b_3706_);
return v_x_3707_;
}
else
{
lean_object* v_key_3708_; lean_object* v_value_3709_; lean_object* v_tail_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3724_; 
v_key_3708_ = lean_ctor_get(v_x_3707_, 0);
v_value_3709_ = lean_ctor_get(v_x_3707_, 1);
v_tail_3710_ = lean_ctor_get(v_x_3707_, 2);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_x_3707_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3712_ = v_x_3707_;
v_isShared_3713_ = v_isSharedCheck_3724_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_tail_3710_);
lean_inc(v_value_3709_);
lean_inc(v_key_3708_);
lean_dec(v_x_3707_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3724_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
uint64_t v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = lean_unbox_uint64(v_key_3708_);
v___x_3715_ = lean_uint64_dec_eq(v___x_3714_, v_a_3705_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
v___x_3716_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3705_, v_b_3706_, v_tail_3710_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 2, v___x_3716_);
v___x_3718_ = v___x_3712_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_key_3708_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_value_3709_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_dec(v_value_3709_);
lean_dec(v_key_3708_);
v___x_3720_ = lean_box_uint64(v_a_3705_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 1, v_b_3706_);
lean_ctor_set(v___x_3712_, 0, v___x_3720_);
v___x_3722_ = v___x_3712_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_b_3706_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_tail_3710_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3725_, lean_object* v_b_3726_, lean_object* v_x_3727_){
_start:
{
uint64_t v_a_boxed_3728_; lean_object* v_res_3729_; 
v_a_boxed_3728_ = lean_unbox_uint64(v_a_3725_);
lean_dec_ref(v_a_3725_);
v_res_3729_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3728_, v_b_3726_, v_x_3727_);
return v_res_3729_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3730_, lean_object* v_x_3731_){
_start:
{
if (lean_obj_tag(v_x_3731_) == 0)
{
uint8_t v___x_3732_; 
v___x_3732_ = 0;
return v___x_3732_;
}
else
{
lean_object* v_key_3733_; lean_object* v_tail_3734_; uint64_t v___x_3735_; uint8_t v___x_3736_; 
v_key_3733_ = lean_ctor_get(v_x_3731_, 0);
v_tail_3734_ = lean_ctor_get(v_x_3731_, 2);
v___x_3735_ = lean_unbox_uint64(v_key_3733_);
v___x_3736_ = lean_uint64_dec_eq(v___x_3735_, v_a_3730_);
if (v___x_3736_ == 0)
{
v_x_3731_ = v_tail_3734_;
goto _start;
}
else
{
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3738_, lean_object* v_x_3739_){
_start:
{
uint64_t v_a_boxed_3740_; uint8_t v_res_3741_; lean_object* v_r_3742_; 
v_a_boxed_3740_ = lean_unbox_uint64(v_a_3738_);
lean_dec_ref(v_a_3738_);
v_res_3741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3740_, v_x_3739_);
lean_dec(v_x_3739_);
v_r_3742_ = lean_box(v_res_3741_);
return v_r_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3743_, uint64_t v_a_3744_, lean_object* v_b_3745_){
_start:
{
lean_object* v_size_3746_; lean_object* v_buckets_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3790_; 
v_size_3746_ = lean_ctor_get(v_m_3743_, 0);
v_buckets_3747_ = lean_ctor_get(v_m_3743_, 1);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_m_3743_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3749_ = v_m_3743_;
v_isShared_3750_ = v_isSharedCheck_3790_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_buckets_3747_);
lean_inc(v_size_3746_);
lean_dec(v_m_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3790_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; uint64_t v___x_3752_; uint64_t v___x_3753_; uint64_t v_fold_3754_; uint64_t v___x_3755_; uint64_t v___x_3756_; uint64_t v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; lean_object* v_bkt_3763_; uint8_t v___x_3764_; 
v___x_3751_ = lean_array_get_size(v_buckets_3747_);
v___x_3752_ = 32ULL;
v___x_3753_ = lean_uint64_shift_right(v_a_3744_, v___x_3752_);
v_fold_3754_ = lean_uint64_xor(v_a_3744_, v___x_3753_);
v___x_3755_ = 16ULL;
v___x_3756_ = lean_uint64_shift_right(v_fold_3754_, v___x_3755_);
v___x_3757_ = lean_uint64_xor(v_fold_3754_, v___x_3756_);
v___x_3758_ = lean_uint64_to_usize(v___x_3757_);
v___x_3759_ = lean_usize_of_nat(v___x_3751_);
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_sub(v___x_3759_, v___x_3760_);
v___x_3762_ = lean_usize_land(v___x_3758_, v___x_3761_);
v_bkt_3763_ = lean_array_uget_borrowed(v_buckets_3747_, v___x_3762_);
v___x_3764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3744_, v_bkt_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v_size_x27_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v_buckets_x27_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3765_ = lean_unsigned_to_nat(1u);
v_size_x27_3766_ = lean_nat_add(v_size_3746_, v___x_3765_);
lean_dec(v_size_3746_);
v___x_3767_ = lean_box_uint64(v_a_3744_);
lean_inc(v_bkt_3763_);
v___x_3768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
lean_ctor_set(v___x_3768_, 1, v_b_3745_);
lean_ctor_set(v___x_3768_, 2, v_bkt_3763_);
v_buckets_x27_3769_ = lean_array_uset(v_buckets_3747_, v___x_3762_, v___x_3768_);
v___x_3770_ = lean_unsigned_to_nat(4u);
v___x_3771_ = lean_nat_mul(v_size_x27_3766_, v___x_3770_);
v___x_3772_ = lean_unsigned_to_nat(3u);
v___x_3773_ = lean_nat_div(v___x_3771_, v___x_3772_);
lean_dec(v___x_3771_);
v___x_3774_ = lean_array_get_size(v_buckets_x27_3769_);
v___x_3775_ = lean_nat_dec_le(v___x_3773_, v___x_3774_);
lean_dec(v___x_3773_);
if (v___x_3775_ == 0)
{
lean_object* v_val_3776_; lean_object* v___x_3778_; 
v_val_3776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3769_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v_val_3776_);
lean_ctor_set(v___x_3749_, 0, v_size_x27_3766_);
v___x_3778_ = v___x_3749_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_size_x27_3766_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_val_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
else
{
lean_object* v___x_3781_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v_buckets_x27_3769_);
lean_ctor_set(v___x_3749_, 0, v_size_x27_3766_);
v___x_3781_ = v___x_3749_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_size_x27_3766_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_buckets_x27_3769_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
else
{
lean_object* v___x_3783_; lean_object* v_buckets_x27_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
lean_inc(v_bkt_3763_);
v___x_3783_ = lean_box(0);
v_buckets_x27_3784_ = lean_array_uset(v_buckets_3747_, v___x_3762_, v___x_3783_);
v___x_3785_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3744_, v_b_3745_, v_bkt_3763_);
v___x_3786_ = lean_array_uset(v_buckets_x27_3784_, v___x_3762_, v___x_3785_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v___x_3786_);
v___x_3788_ = v___x_3749_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_size_3746_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3791_, lean_object* v_a_3792_, lean_object* v_b_3793_){
_start:
{
uint64_t v_a_boxed_3794_; lean_object* v_res_3795_; 
v_a_boxed_3794_ = lean_unbox_uint64(v_a_3792_);
lean_dec_ref(v_a_3792_);
v_res_3795_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3791_, v_a_boxed_3794_, v_b_3793_);
return v_res_3795_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = lean_box(0);
v___x_3797_ = lean_unsigned_to_nat(16u);
v___x_3798_ = lean_mk_array(v___x_3797_, v___x_3796_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v_found_3801_; 
v___x_3799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3800_ = lean_unsigned_to_nat(0u);
v_found_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3801_, 0, v___x_3800_);
lean_ctor_set(v_found_3801_, 1, v___x_3799_);
return v_found_3801_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_found_3802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3803_ = lean_box(0);
v___x_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
lean_ctor_set(v___x_3804_, 1, v_found_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3805_, lean_object* v_numDigits_3806_, lean_object* v_es_3807_, lean_object* v_as_3808_, size_t v_sz_3809_, size_t v_i_3810_, lean_object* v_b_3811_){
_start:
{
lean_object* v_a_3813_; uint8_t v___x_3817_; 
v___x_3817_ = lean_usize_dec_lt(v_i_3810_, v_sz_3809_);
if (v___x_3817_ == 0)
{
return v_b_3811_;
}
else
{
lean_object* v_snd_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3852_; 
v_snd_3818_ = lean_ctor_get(v_b_3811_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_b_3811_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; 
v_unused_3853_ = lean_ctor_get(v_b_3811_, 0);
lean_dec(v_unused_3853_);
v___x_3820_ = v_b_3811_;
v_isShared_3821_ = v_isSharedCheck_3852_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_snd_3818_);
lean_dec(v_b_3811_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3852_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v_a_3822_; uint64_t v_anchor_3823_; lean_object* v___x_3824_; uint64_t v___x_3825_; uint64_t v___x_3826_; lean_object* v___x_3827_; 
v_a_3822_ = lean_array_uget_borrowed(v_as_3808_, v_i_3810_);
v_anchor_3823_ = lean_ctor_get_uint64(v_a_3822_, sizeof(void*)*3);
v___x_3824_ = lean_box(0);
v___x_3825_ = lean_uint64_of_nat(v_shift_3805_);
v___x_3826_ = lean_uint64_shift_right(v_anchor_3823_, v___x_3825_);
v___x_3827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3818_, v___x_3826_);
if (lean_obj_tag(v___x_3827_) == 1)
{
lean_object* v_val_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3846_; 
v_val_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3846_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_val_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3846_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
uint64_t v___x_3832_; uint8_t v___x_3833_; 
v___x_3832_ = lean_unbox_uint64(v_val_3828_);
lean_dec(v_val_3828_);
v___x_3833_ = lean_uint64_dec_eq(v___x_3832_, v_anchor_3823_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3834_ = lean_unsigned_to_nat(1u);
v___x_3835_ = lean_nat_add(v_numDigits_3806_, v___x_3834_);
v___x_3836_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3807_, v___x_3835_);
lean_dec(v___x_3835_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3836_);
v___x_3838_ = v___x_3830_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3838_);
v___x_3840_ = v___x_3820_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_snd_3818_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
else
{
lean_object* v___x_3844_; 
lean_del_object(v___x_3830_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3824_);
v___x_3844_ = v___x_3820_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_snd_3818_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
v_a_3813_ = v___x_3844_;
goto v___jp_3812_;
}
}
}
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec(v___x_3827_);
v___x_3847_ = lean_box_uint64(v_anchor_3823_);
v___x_3848_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3818_, v___x_3826_, v___x_3847_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 1, v___x_3848_);
lean_ctor_set(v___x_3820_, 0, v___x_3824_);
v___x_3850_ = v___x_3820_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
v_a_3813_ = v___x_3850_;
goto v___jp_3812_;
}
}
}
}
v___jp_3812_:
{
size_t v___x_3814_; size_t v___x_3815_; 
v___x_3814_ = ((size_t)1ULL);
v___x_3815_ = lean_usize_add(v_i_3810_, v___x_3814_);
v_i_3810_ = v___x_3815_;
v_b_3811_ = v_a_3813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3854_, lean_object* v_numDigits_3855_){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3856_ = lean_unsigned_to_nat(4u);
v___x_3857_ = lean_nat_mul(v___x_3856_, v_numDigits_3855_);
v___x_3858_ = lean_unsigned_to_nat(64u);
v___x_3859_ = lean_nat_dec_lt(v___x_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_dec(v___x_3857_);
lean_inc(v_numDigits_3855_);
return v_numDigits_3855_;
}
else
{
lean_object* v_shift_3860_; lean_object* v___x_3861_; size_t v_sz_3862_; size_t v___x_3863_; lean_object* v___x_3864_; lean_object* v_fst_3865_; 
v_shift_3860_ = lean_nat_sub(v___x_3858_, v___x_3857_);
lean_dec(v___x_3857_);
v___x_3861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3862_ = lean_array_size(v_es_3854_);
v___x_3863_ = ((size_t)0ULL);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3860_, v_numDigits_3855_, v_es_3854_, v_es_3854_, v_sz_3862_, v___x_3863_, v___x_3861_);
lean_dec(v_shift_3860_);
v_fst_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_fst_3865_);
lean_dec_ref(v___x_3864_);
if (lean_obj_tag(v_fst_3865_) == 0)
{
lean_inc(v_numDigits_3855_);
return v_numDigits_3855_;
}
else
{
lean_object* v_val_3866_; 
v_val_3866_ = lean_ctor_get(v_fst_3865_, 0);
lean_inc(v_val_3866_);
lean_dec_ref_known(v_fst_3865_, 1);
return v_val_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3867_, lean_object* v_numDigits_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3867_, v_numDigits_3868_);
lean_dec(v_numDigits_3868_);
lean_dec_ref(v_es_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3870_, lean_object* v_numDigits_3871_, lean_object* v_es_3872_, lean_object* v_as_3873_, lean_object* v_sz_3874_, lean_object* v_i_3875_, lean_object* v_b_3876_){
_start:
{
size_t v_sz_boxed_3877_; size_t v_i_boxed_3878_; lean_object* v_res_3879_; 
v_sz_boxed_3877_ = lean_unbox_usize(v_sz_3874_);
lean_dec(v_sz_3874_);
v_i_boxed_3878_ = lean_unbox_usize(v_i_3875_);
lean_dec(v_i_3875_);
v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3870_, v_numDigits_3871_, v_es_3872_, v_as_3873_, v_sz_boxed_3877_, v_i_boxed_3878_, v_b_3876_);
lean_dec_ref(v_as_3873_);
lean_dec_ref(v_es_3872_);
lean_dec(v_numDigits_3871_);
lean_dec(v_shift_3870_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3880_){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_unsigned_to_nat(4u);
v___x_3882_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3880_, v___x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3883_);
lean_dec_ref(v_es_3883_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3885_, lean_object* v_as_3886_, size_t v_i_3887_, size_t v_stop_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_a_3902_; uint8_t v___x_3906_; 
v___x_3906_ = lean_usize_dec_eq(v_i_3887_, v_stop_3888_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v_e_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_array_uget_borrowed(v_as_3886_, v_i_3887_);
v_e_3908_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3907_);
v___x_3909_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3907_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
lean_inc(v___x_3907_);
v___x_3911_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3907_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
if (lean_obj_tag(v_a_3912_) == 2)
{
lean_object* v_numCases_3913_; uint8_t v_isRec_3914_; lean_object* v___x_3915_; 
v_numCases_3913_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_numCases_3913_);
v_isRec_3914_ = lean_ctor_get_uint8(v_a_3912_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3912_, 1);
lean_inc_ref(v_filter_3885_);
lean_inc(v___y_3899_);
lean_inc_ref(v___y_3898_);
lean_inc(v___y_3897_);
lean_inc_ref(v___y_3896_);
lean_inc(v___y_3895_);
lean_inc_ref(v___y_3894_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc(v___y_3890_);
lean_inc_ref(v_e_3908_);
v___x_3915_ = lean_apply_12(v_filter_3885_, v_e_3908_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, lean_box(0));
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; uint8_t v___x_3917_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = lean_unbox(v_a_3916_);
lean_dec(v_a_3916_);
if (v___x_3917_ == 0)
{
lean_dec(v_numCases_3913_);
lean_dec(v_a_3910_);
lean_dec_ref(v_e_3908_);
v_a_3902_ = v_b_3889_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3918_; uint64_t v___x_3919_; lean_object* v___x_3920_; 
lean_inc(v___x_3907_);
v___x_3918_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3918_, 0, v___x_3907_);
lean_ctor_set(v___x_3918_, 1, v_numCases_3913_);
lean_ctor_set(v___x_3918_, 2, v_e_3908_);
lean_ctor_set_uint8(v___x_3918_, sizeof(void*)*3 + 8, v_isRec_3914_);
v___x_3919_ = lean_unbox_uint64(v_a_3910_);
lean_dec(v_a_3910_);
lean_ctor_set_uint64(v___x_3918_, sizeof(void*)*3, v___x_3919_);
v___x_3920_ = lean_array_push(v_b_3889_, v___x_3918_);
v_a_3902_ = v___x_3920_;
goto v___jp_3901_;
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_numCases_3913_);
lean_dec(v_a_3910_);
lean_dec_ref(v_e_3908_);
lean_dec_ref(v_b_3889_);
lean_dec_ref(v_filter_3885_);
v_a_3921_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3915_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3915_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_dec(v_a_3912_);
lean_dec(v_a_3910_);
lean_dec_ref(v_e_3908_);
v_a_3902_ = v_b_3889_;
goto v___jp_3901_;
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_a_3910_);
lean_dec_ref(v_e_3908_);
lean_dec_ref(v_b_3889_);
lean_dec_ref(v_filter_3885_);
v_a_3929_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3911_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3911_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec_ref(v_e_3908_);
lean_dec_ref(v_b_3889_);
lean_dec_ref(v_filter_3885_);
v_a_3937_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3909_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3909_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
else
{
lean_object* v___x_3945_; 
lean_dec_ref(v_filter_3885_);
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_b_3889_);
return v___x_3945_;
}
v___jp_3901_:
{
size_t v___x_3903_; size_t v___x_3904_; 
v___x_3903_ = ((size_t)1ULL);
v___x_3904_ = lean_usize_add(v_i_3887_, v___x_3903_);
v_i_3887_ = v___x_3904_;
v_b_3889_ = v_a_3902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3946_, lean_object* v_as_3947_, lean_object* v_i_3948_, lean_object* v_stop_3949_, lean_object* v_b_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
size_t v_i_boxed_3962_; size_t v_stop_boxed_3963_; lean_object* v_res_3964_; 
v_i_boxed_3962_ = lean_unbox_usize(v_i_3948_);
lean_dec(v_i_3948_);
v_stop_boxed_3963_ = lean_unbox_usize(v_stop_3949_);
lean_dec(v_stop_3949_);
v_res_3964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3946_, v_as_3947_, v_i_boxed_3962_, v_stop_boxed_3963_, v_b_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v_as_3947_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3967_, lean_object* v_as_3968_, lean_object* v_start_3969_, lean_object* v_stop_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3983_ = lean_nat_dec_lt(v_start_3969_, v_stop_3970_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; 
lean_dec_ref(v_filter_3967_);
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
return v___x_3984_;
}
else
{
lean_object* v___x_3985_; uint8_t v___x_3986_; 
v___x_3985_ = lean_array_get_size(v_as_3968_);
v___x_3986_ = lean_nat_dec_le(v_stop_3970_, v___x_3985_);
if (v___x_3986_ == 0)
{
uint8_t v___x_3987_; 
v___x_3987_ = lean_nat_dec_lt(v_start_3969_, v___x_3985_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; 
lean_dec_ref(v_filter_3967_);
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3982_);
return v___x_3988_;
}
else
{
size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = lean_usize_of_nat(v_start_3969_);
v___x_3990_ = lean_usize_of_nat(v___x_3985_);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3967_, v_as_3968_, v___x_3989_, v___x_3990_, v___x_3982_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
return v___x_3991_;
}
}
else
{
size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = lean_usize_of_nat(v_start_3969_);
v___x_3993_ = lean_usize_of_nat(v_stop_3970_);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3967_, v_as_3968_, v___x_3992_, v___x_3993_, v___x_3982_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
return v___x_3994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3995_, lean_object* v_as_3996_, lean_object* v_start_3997_, lean_object* v_stop_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3995_, v_as_3996_, v_start_3997_, v_stop_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec(v_stop_3998_);
lean_dec(v_start_3997_);
lean_dec_ref(v_as_3996_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_4011_, lean_object* v_candidates_x3f_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_candidates_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; 
if (lean_obj_tag(v_candidates_x3f_4012_) == 0)
{
lean_object* v___x_4058_; lean_object* v_toGoalState_4059_; lean_object* v_split_4060_; lean_object* v_candidates_4061_; 
v___x_4058_ = lean_st_ref_get(v_a_4013_);
v_toGoalState_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc_ref(v_toGoalState_4059_);
lean_dec(v___x_4058_);
v_split_4060_ = lean_ctor_get(v_toGoalState_4059_, 15);
lean_inc_ref(v_split_4060_);
lean_dec_ref(v_toGoalState_4059_);
v_candidates_4061_ = lean_ctor_get(v_split_4060_, 0);
lean_inc(v_candidates_4061_);
lean_dec_ref(v_split_4060_);
v_candidates_4025_ = v_candidates_4061_;
v___y_4026_ = v_a_4013_;
v___y_4027_ = v_a_4014_;
v___y_4028_ = v_a_4015_;
v___y_4029_ = v_a_4016_;
v___y_4030_ = v_a_4017_;
v___y_4031_ = v_a_4018_;
v___y_4032_ = v_a_4019_;
v___y_4033_ = v_a_4020_;
v___y_4034_ = v_a_4021_;
v___y_4035_ = v_a_4022_;
goto v___jp_4024_;
}
else
{
lean_object* v_val_4062_; 
v_val_4062_ = lean_ctor_get(v_candidates_x3f_4012_, 0);
lean_inc(v_val_4062_);
lean_dec_ref_known(v_candidates_x3f_4012_, 1);
v_candidates_4025_ = v_val_4062_;
v___y_4026_ = v_a_4013_;
v___y_4027_ = v_a_4014_;
v___y_4028_ = v_a_4015_;
v___y_4029_ = v_a_4016_;
v___y_4030_ = v_a_4017_;
v___y_4031_ = v_a_4018_;
v___y_4032_ = v_a_4019_;
v___y_4033_ = v_a_4020_;
v___y_4034_ = v_a_4021_;
v___y_4035_ = v_a_4022_;
goto v___jp_4024_;
}
v___jp_4024_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4036_ = lean_array_mk(v_candidates_4025_);
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = lean_array_get_size(v___x_4036_);
v___x_4039_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_4011_, v___x_4036_, v___x_4037_, v___x_4038_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec_ref(v___x_4036_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4049_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4042_ = v___x_4039_;
v_isShared_4043_ = v_isSharedCheck_4049_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4039_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4049_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4044_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4040_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v_a_4040_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4045_);
v___x_4047_ = v___x_4042_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4039_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4039_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4063_, lean_object* v_candidates_x3f_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4063_, v_candidates_x3f_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
lean_dec(v_a_4065_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4077_, lean_object* v_m_4078_, uint64_t v_a_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4078_, v_a_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4081_, lean_object* v_m_4082_, lean_object* v_a_4083_){
_start:
{
uint64_t v_a_boxed_4084_; lean_object* v_res_4085_; 
v_a_boxed_4084_ = lean_unbox_uint64(v_a_4083_);
lean_dec_ref(v_a_4083_);
v_res_4085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4081_, v_m_4082_, v_a_boxed_4084_);
lean_dec_ref(v_m_4082_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4086_, lean_object* v_m_4087_, uint64_t v_a_4088_, lean_object* v_b_4089_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4087_, v_a_4088_, v_b_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4091_, lean_object* v_m_4092_, lean_object* v_a_4093_, lean_object* v_b_4094_){
_start:
{
uint64_t v_a_boxed_4095_; lean_object* v_res_4096_; 
v_a_boxed_4095_ = lean_unbox_uint64(v_a_4093_);
lean_dec_ref(v_a_4093_);
v_res_4096_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4091_, v_m_4092_, v_a_boxed_4095_, v_b_4094_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4097_, uint64_t v_a_4098_, lean_object* v_x_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4098_, v_x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4101_, lean_object* v_a_4102_, lean_object* v_x_4103_){
_start:
{
uint64_t v_a_boxed_4104_; lean_object* v_res_4105_; 
v_a_boxed_4104_ = lean_unbox_uint64(v_a_4102_);
lean_dec_ref(v_a_4102_);
v_res_4105_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4101_, v_a_boxed_4104_, v_x_4103_);
lean_dec(v_x_4103_);
return v_res_4105_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4106_, uint64_t v_a_4107_, lean_object* v_x_4108_){
_start:
{
uint8_t v___x_4109_; 
v___x_4109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4107_, v_x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4110_, lean_object* v_a_4111_, lean_object* v_x_4112_){
_start:
{
uint64_t v_a_boxed_4113_; uint8_t v_res_4114_; lean_object* v_r_4115_; 
v_a_boxed_4113_ = lean_unbox_uint64(v_a_4111_);
lean_dec_ref(v_a_4111_);
v_res_4114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4110_, v_a_boxed_4113_, v_x_4112_);
lean_dec(v_x_4112_);
v_r_4115_ = lean_box(v_res_4114_);
return v_r_4115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4116_, lean_object* v_data_4117_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4119_, uint64_t v_a_4120_, lean_object* v_b_4121_, lean_object* v_x_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4120_, v_b_4121_, v_x_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4124_, lean_object* v_a_4125_, lean_object* v_b_4126_, lean_object* v_x_4127_){
_start:
{
uint64_t v_a_boxed_4128_; lean_object* v_res_4129_; 
v_a_boxed_4128_ = lean_unbox_uint64(v_a_4125_);
lean_dec_ref(v_a_4125_);
v_res_4129_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4124_, v_a_boxed_4128_, v_b_4126_, v_x_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4130_, lean_object* v_i_4131_, lean_object* v_source_4132_, lean_object* v_target_4133_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4131_, v_source_4132_, v_target_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4135_, lean_object* v_x_4136_, lean_object* v_x_4137_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4136_, v_x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
uint8_t v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4151_ = 1;
v___x_4152_ = lean_box(v___x_4151_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v_x_4154_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4167_, uint64_t v_a_4168_, lean_object* v_c_4169_, lean_object* v_numDigits_4170_, lean_object* v_as_4171_, size_t v_sz_4172_, size_t v_i_4173_, lean_object* v_b_4174_){
_start:
{
lean_object* v_a_4177_; uint8_t v___x_4181_; 
v___x_4181_ = lean_usize_dec_lt(v_i_4173_, v_sz_4172_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec(v_numDigits_4170_);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v_b_4174_);
return v___x_4182_;
}
else
{
lean_object* v_snd_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4209_; 
v_snd_4183_ = lean_ctor_get(v_b_4174_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_b_4174_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; 
v_unused_4210_ = lean_ctor_get(v_b_4174_, 0);
lean_dec(v_unused_4210_);
v___x_4185_ = v_b_4174_;
v_isShared_4186_ = v_isSharedCheck_4209_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_snd_4183_);
lean_dec(v_b_4174_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4209_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v_a_4187_; lean_object* v_c_4188_; uint64_t v_anchor_4189_; lean_object* v___x_4190_; uint64_t v___x_4191_; uint64_t v___x_4192_; uint8_t v___x_4193_; 
v_a_4187_ = lean_array_uget_borrowed(v_as_4171_, v_i_4173_);
v_c_4188_ = lean_ctor_get(v_a_4187_, 0);
v_anchor_4189_ = lean_ctor_get_uint64(v_a_4187_, sizeof(void*)*3);
v___x_4190_ = lean_box(0);
v___x_4191_ = lean_uint64_shift_right(v_anchor_4189_, v___x_4167_);
v___x_4192_ = lean_uint64_shift_right(v_a_4168_, v___x_4167_);
v___x_4193_ = lean_uint64_dec_eq(v___x_4191_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4195_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4190_);
v___x_4195_ = v___x_4185_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_snd_4183_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
v_a_4177_ = v___x_4195_;
goto v___jp_4176_;
}
}
else
{
uint8_t v___x_4197_; 
v___x_4197_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4188_, v_c_4169_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4198_ = lean_unsigned_to_nat(1u);
v___x_4199_ = lean_nat_add(v_snd_4183_, v___x_4198_);
lean_dec(v_snd_4183_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v___x_4199_);
lean_ctor_set(v___x_4185_, 0, v___x_4190_);
v___x_4201_ = v___x_4185_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
v_a_4177_ = v___x_4201_;
goto v___jp_4176_;
}
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4206_; 
lean_inc(v_snd_4183_);
v___x_4203_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4203_, 0, v_numDigits_4170_);
lean_ctor_set(v___x_4203_, 1, v_snd_4183_);
lean_ctor_set_uint64(v___x_4203_, sizeof(void*)*2, v_a_4168_);
v___x_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4204_);
v___x_4206_ = v___x_4185_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_snd_4183_);
v___x_4206_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
}
}
v___jp_4176_:
{
size_t v___x_4178_; size_t v___x_4179_; 
v___x_4178_ = ((size_t)1ULL);
v___x_4179_ = lean_usize_add(v_i_4173_, v___x_4178_);
v_i_4173_ = v___x_4179_;
v_b_4174_ = v_a_4177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4211_, lean_object* v_a_4212_, lean_object* v_c_4213_, lean_object* v_numDigits_4214_, lean_object* v_as_4215_, lean_object* v_sz_4216_, lean_object* v_i_4217_, lean_object* v_b_4218_, lean_object* v___y_4219_){
_start:
{
uint64_t v___x_7694__boxed_4220_; uint64_t v_a_7695__boxed_4221_; size_t v_sz_boxed_4222_; size_t v_i_boxed_4223_; lean_object* v_res_4224_; 
v___x_7694__boxed_4220_ = lean_unbox_uint64(v___x_4211_);
lean_dec_ref(v___x_4211_);
v_a_7695__boxed_4221_ = lean_unbox_uint64(v_a_4212_);
lean_dec_ref(v_a_4212_);
v_sz_boxed_4222_ = lean_unbox_usize(v_sz_4216_);
lean_dec(v_sz_4216_);
v_i_boxed_4223_ = lean_unbox_usize(v_i_4217_);
lean_dec(v_i_4217_);
v_res_4224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7694__boxed_4220_, v_a_7695__boxed_4221_, v_c_4213_, v_numDigits_4214_, v_as_4215_, v_sz_boxed_4222_, v_i_boxed_4223_, v_b_4218_);
lean_dec_ref(v_as_4215_);
lean_dec_ref(v_c_4213_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4229_, lean_object* v_candidates_x3f_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v___f_4242_; lean_object* v___x_4243_; 
v___f_4242_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4243_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4242_, v_candidates_x3f_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v_candidates_4245_; lean_object* v_numDigits_4246_; lean_object* v___x_4247_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v_candidates_4245_ = lean_ctor_get(v_a_4244_, 0);
lean_inc_ref(v_candidates_4245_);
v_numDigits_4246_ = lean_ctor_get(v_a_4244_, 1);
lean_inc(v_numDigits_4246_);
lean_dec(v_a_4244_);
v___x_4247_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4229_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; uint64_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; size_t v_sz_4256_; size_t v___x_4257_; uint64_t v___x_4258_; lean_object* v___x_4259_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
v___x_4249_ = lean_unsigned_to_nat(64u);
v___x_4250_ = lean_unsigned_to_nat(4u);
v___x_4251_ = lean_nat_mul(v___x_4250_, v_numDigits_4246_);
v___x_4252_ = lean_nat_sub(v___x_4249_, v___x_4251_);
lean_dec(v___x_4251_);
v___x_4253_ = lean_uint64_of_nat(v___x_4252_);
lean_dec(v___x_4252_);
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4256_ = lean_array_size(v_candidates_4245_);
v___x_4257_ = ((size_t)0ULL);
v___x_4258_ = lean_unbox_uint64(v_a_4248_);
lean_inc(v_numDigits_4246_);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4253_, v___x_4258_, v_c_4229_, v_numDigits_4246_, v_candidates_4245_, v_sz_4256_, v___x_4257_, v___x_4255_);
lean_dec_ref(v_candidates_4245_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4274_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4274_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4274_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v_fst_4264_; 
v_fst_4264_ = lean_ctor_get(v_a_4260_, 0);
lean_inc(v_fst_4264_);
lean_dec(v_a_4260_);
if (lean_obj_tag(v_fst_4264_) == 0)
{
lean_object* v___x_4265_; uint64_t v___x_4266_; lean_object* v___x_4268_; 
v___x_4265_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4265_, 0, v_numDigits_4246_);
lean_ctor_set(v___x_4265_, 1, v___x_4254_);
v___x_4266_ = lean_unbox_uint64(v_a_4248_);
lean_dec(v_a_4248_);
lean_ctor_set_uint64(v___x_4265_, sizeof(void*)*2, v___x_4266_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___x_4265_);
v___x_4268_ = v___x_4262_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4265_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
else
{
lean_object* v_val_4270_; lean_object* v___x_4272_; 
lean_dec(v_a_4248_);
lean_dec(v_numDigits_4246_);
v_val_4270_ = lean_ctor_get(v_fst_4264_, 0);
lean_inc(v_val_4270_);
lean_dec_ref_known(v_fst_4264_, 1);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v_val_4270_);
v___x_4272_ = v___x_4262_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_val_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_a_4248_);
lean_dec(v_numDigits_4246_);
v_a_4275_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4259_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4259_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_numDigits_4246_);
lean_dec_ref(v_candidates_4245_);
v_a_4283_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4247_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4247_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_a_4291_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4243_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4243_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4299_, lean_object* v_candidates_x3f_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4299_, v_candidates_x3f_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_c_4299_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4313_, uint64_t v_a_4314_, lean_object* v_c_4315_, lean_object* v_numDigits_4316_, lean_object* v_as_4317_, size_t v_sz_4318_, size_t v_i_4319_, lean_object* v_b_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4313_, v_a_4314_, v_c_4315_, v_numDigits_4316_, v_as_4317_, v_sz_4318_, v_i_4319_, v_b_4320_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4333_ = _args[0];
lean_object* v_a_4334_ = _args[1];
lean_object* v_c_4335_ = _args[2];
lean_object* v_numDigits_4336_ = _args[3];
lean_object* v_as_4337_ = _args[4];
lean_object* v_sz_4338_ = _args[5];
lean_object* v_i_4339_ = _args[6];
lean_object* v_b_4340_ = _args[7];
lean_object* v___y_4341_ = _args[8];
lean_object* v___y_4342_ = _args[9];
lean_object* v___y_4343_ = _args[10];
lean_object* v___y_4344_ = _args[11];
lean_object* v___y_4345_ = _args[12];
lean_object* v___y_4346_ = _args[13];
lean_object* v___y_4347_ = _args[14];
lean_object* v___y_4348_ = _args[15];
lean_object* v___y_4349_ = _args[16];
lean_object* v___y_4350_ = _args[17];
lean_object* v___y_4351_ = _args[18];
_start:
{
uint64_t v___x_7893__boxed_4352_; uint64_t v_a_7894__boxed_4353_; size_t v_sz_boxed_4354_; size_t v_i_boxed_4355_; lean_object* v_res_4356_; 
v___x_7893__boxed_4352_ = lean_unbox_uint64(v___x_4333_);
lean_dec_ref(v___x_4333_);
v_a_7894__boxed_4353_ = lean_unbox_uint64(v_a_4334_);
lean_dec_ref(v_a_4334_);
v_sz_boxed_4354_ = lean_unbox_usize(v_sz_4338_);
lean_dec(v_sz_4338_);
v_i_boxed_4355_ = lean_unbox_usize(v_i_4339_);
lean_dec(v_i_4339_);
v_res_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7893__boxed_4352_, v_a_7894__boxed_4353_, v_c_4335_, v_numDigits_4336_, v_as_4337_, v_sz_boxed_4354_, v_i_boxed_4355_, v_b_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec_ref(v_as_4337_);
lean_dec_ref(v_c_4335_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_numDigits_4384_; uint64_t v_anchor_4385_; lean_object* v_ordinal_4386_; lean_object* v___x_4387_; 
v_numDigits_4384_ = lean_ctor_get(v_info_4381_, 0);
v_anchor_4385_ = lean_ctor_get_uint64(v_info_4381_, sizeof(void*)*2);
v_ordinal_4386_ = lean_ctor_get(v_info_4381_, 1);
v___x_4387_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4384_, v_anchor_4385_, v_a_4382_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4424_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4424_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4424_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4392_ = lean_unsigned_to_nat(0u);
v___x_4393_ = lean_nat_dec_eq(v_ordinal_4386_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v_ref_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4410_; 
v_ref_4394_ = lean_ctor_get(v_a_4382_, 2);
v___x_4395_ = l_Lean_SourceInfo_fromRef(v_ref_4394_, v___x_4393_);
v___x_4396_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4397_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4395_, 3);
v___x_4398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4395_);
lean_ctor_set(v___x_4398_, 1, v___x_4396_);
v___x_4399_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4400_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4395_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = lean_unsigned_to_nat(1u);
v___x_4403_ = lean_nat_add(v_ordinal_4386_, v___x_4402_);
v___x_4404_ = l_Nat_reprFast(v___x_4403_);
v___x_4405_ = lean_box(2);
v___x_4406_ = l_Lean_Syntax_mkNumLit(v___x_4404_, v___x_4405_);
v___x_4407_ = l_Lean_Syntax_node3(v___x_4395_, v___x_4399_, v_a_4388_, v___x_4401_, v___x_4406_);
v___x_4408_ = l_Lean_Syntax_node2(v___x_4395_, v___x_4397_, v___x_4398_, v___x_4407_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v___x_4408_);
v___x_4410_ = v___x_4390_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
else
{
lean_object* v_ref_4412_; uint8_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v_ref_4412_ = lean_ctor_get(v_a_4382_, 2);
v___x_4413_ = 0;
v___x_4414_ = l_Lean_SourceInfo_fromRef(v_ref_4412_, v___x_4413_);
v___x_4415_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4416_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4414_, 2);
v___x_4417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4414_);
lean_ctor_set(v___x_4417_, 1, v___x_4415_);
v___x_4418_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4419_ = l_Lean_Syntax_node1(v___x_4414_, v___x_4418_, v_a_4388_);
v___x_4420_ = l_Lean_Syntax_node2(v___x_4414_, v___x_4416_, v___x_4417_, v___x_4419_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v___x_4420_);
v___x_4422_ = v___x_4390_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
else
{
return v___x_4387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4425_, v_a_4426_);
lean_dec_ref(v_a_4426_);
lean_dec_ref(v_info_4425_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4429_, v_a_4430_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4434_, v_a_4435_, v_a_4436_);
lean_dec(v_a_4436_);
lean_dec_ref(v_a_4435_);
lean_dec_ref(v_info_4434_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(lean_object* v_proof_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v_p_4470_; lean_object* v___x_4473_; 
lean_inc_ref(v_proof_4451_);
v___x_4473_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4451_, v_a_4453_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4500_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4476_ = v___x_4473_;
v_isShared_4477_ = v_isSharedCheck_4500_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4473_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4500_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = l_Lean_Expr_cleanupAnnotations(v_a_4474_);
lean_dec(v_a_4474_);
v___x_4479_ = l_Lean_Expr_isApp(v___x_4478_);
if (v___x_4479_ == 0)
{
lean_dec_ref(v___x_4478_);
lean_del_object(v___x_4476_);
v___y_4458_ = v_a_4452_;
v___y_4459_ = v_a_4453_;
v___y_4460_ = v_a_4454_;
v___y_4461_ = v_a_4455_;
goto v___jp_4457_;
}
else
{
lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4478_);
v___x_4481_ = l_Lean_Expr_isApp(v___x_4480_);
if (v___x_4481_ == 0)
{
lean_dec_ref(v___x_4480_);
lean_dec_ref(v___x_4478_);
lean_del_object(v___x_4476_);
v___y_4458_ = v_a_4452_;
v___y_4459_ = v_a_4453_;
v___y_4460_ = v_a_4454_;
v___y_4461_ = v_a_4455_;
goto v___jp_4457_;
}
else
{
lean_object* v_arg_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v_arg_4482_ = lean_ctor_get(v___x_4478_, 1);
lean_inc_ref(v_arg_4482_);
lean_dec_ref(v___x_4478_);
v___x_4483_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4480_);
v___x_4484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4485_ = l_Lean_Expr_isConstOf(v___x_4483_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; uint8_t v___x_4487_; 
lean_dec_ref(v___x_4480_);
lean_del_object(v___x_4476_);
v___x_4486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4487_ = l_Lean_Expr_isConstOf(v___x_4483_, v___x_4486_);
if (v___x_4487_ == 0)
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4489_ = l_Lean_Expr_isConstOf(v___x_4483_, v___x_4488_);
lean_dec_ref(v___x_4483_);
if (v___x_4489_ == 0)
{
lean_dec_ref(v_arg_4482_);
v___y_4458_ = v_a_4452_;
v___y_4459_ = v_a_4453_;
v___y_4460_ = v_a_4454_;
v___y_4461_ = v_a_4455_;
goto v___jp_4457_;
}
else
{
lean_dec_ref(v_proof_4451_);
v_p_4470_ = v_arg_4482_;
goto v___jp_4469_;
}
}
else
{
lean_dec_ref(v___x_4483_);
lean_dec_ref(v_proof_4451_);
v_p_4470_ = v_arg_4482_;
goto v___jp_4469_;
}
}
else
{
lean_object* v_arg_4490_; uint8_t v___x_4491_; 
lean_dec_ref(v___x_4483_);
lean_dec_ref(v_proof_4451_);
v_arg_4490_ = lean_ctor_get(v___x_4480_, 1);
lean_inc_ref(v_arg_4490_);
lean_dec_ref(v___x_4480_);
v___x_4491_ = l_Lean_Expr_isFalse(v_arg_4490_);
lean_dec_ref(v_arg_4490_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; lean_object* v___x_4494_; 
lean_dec_ref(v_arg_4482_);
v___x_4492_ = lean_box(0);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 0, v___x_4492_);
v___x_4494_ = v___x_4476_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4496_, 0, v_arg_4482_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 0, v___x_4496_);
v___x_4498_ = v___x_4476_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v_proof_4451_);
v_a_4501_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4473_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4473_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
v___jp_4457_:
{
if (lean_obj_tag(v_proof_4451_) == 6)
{
lean_object* v_body_4462_; uint8_t v___x_4463_; 
v_body_4462_ = lean_ctor_get(v_proof_4451_, 2);
lean_inc_ref(v_body_4462_);
lean_dec_ref_known(v_proof_4451_, 3);
v___x_4463_ = l_Lean_Expr_hasLooseBVars(v_body_4462_);
if (v___x_4463_ == 0)
{
v_proof_4451_ = v_body_4462_;
v_a_4452_ = v___y_4458_;
v_a_4453_ = v___y_4459_;
v_a_4454_ = v___y_4460_;
v_a_4455_ = v___y_4461_;
goto _start;
}
else
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_dec_ref(v_body_4462_);
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
return v___x_4466_;
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_proof_4451_);
v___x_4467_ = lean_box(0);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
}
v___jp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4471_, 0, v_p_4470_);
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
return v___x_4472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___boxed(lean_object* v_proof_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_proof_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(lean_object* v_e_4516_, lean_object* v___y_4517_){
_start:
{
uint8_t v___x_4519_; 
v___x_4519_ = l_Lean_Expr_hasMVar(v_e_4516_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; 
v___x_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4520_, 0, v_e_4516_);
return v___x_4520_;
}
else
{
lean_object* v___x_4521_; lean_object* v_mctx_4522_; lean_object* v___x_4523_; lean_object* v_fst_4524_; lean_object* v_snd_4525_; lean_object* v___x_4526_; lean_object* v_cache_4527_; lean_object* v_zetaDeltaFVarIds_4528_; lean_object* v_postponed_4529_; lean_object* v_diag_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4539_; 
v___x_4521_ = lean_st_ref_get(v___y_4517_);
v_mctx_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc_ref(v_mctx_4522_);
lean_dec(v___x_4521_);
v___x_4523_ = l_Lean_instantiateMVarsCore(v_mctx_4522_, v_e_4516_);
v_fst_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_fst_4524_);
v_snd_4525_ = lean_ctor_get(v___x_4523_, 1);
lean_inc(v_snd_4525_);
lean_dec_ref(v___x_4523_);
v___x_4526_ = lean_st_ref_take(v___y_4517_);
v_cache_4527_ = lean_ctor_get(v___x_4526_, 1);
v_zetaDeltaFVarIds_4528_ = lean_ctor_get(v___x_4526_, 2);
v_postponed_4529_ = lean_ctor_get(v___x_4526_, 3);
v_diag_4530_ = lean_ctor_get(v___x_4526_, 4);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; 
v_unused_4540_ = lean_ctor_get(v___x_4526_, 0);
lean_dec(v_unused_4540_);
v___x_4532_ = v___x_4526_;
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_diag_4530_);
lean_inc(v_postponed_4529_);
lean_inc(v_zetaDeltaFVarIds_4528_);
lean_inc(v_cache_4527_);
lean_dec(v___x_4526_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v_snd_4525_);
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_snd_4525_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_cache_4527_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_zetaDeltaFVarIds_4528_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v_postponed_4529_);
lean_ctor_set(v_reuseFailAlloc_4538_, 4, v_diag_4530_);
v___x_4535_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_st_ref_put(v___y_4517_, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v_fst_4524_);
return v___x_4537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg___boxed(lean_object* v_e_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4541_, v___y_4542_);
lean_dec(v___y_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(lean_object* v_e_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v_e_4545_, v___y_4547_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___boxed(lean_object* v_e_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0(v_e_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(lean_object* v_mvarId_4559_, lean_object* v_x_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4559_, v_x_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4566_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4566_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
v_a_4575_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4566_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4566_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4583_, lean_object* v_x_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4583_, v_x_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(lean_object* v_00_u03b1_4591_, lean_object* v_mvarId_4592_, lean_object* v_x_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4592_, v_x_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___boxed(lean_object* v_00_u03b1_4600_, lean_object* v_mvarId_4601_, lean_object* v_x_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1(v_00_u03b1_4600_, v_mvarId_4601_, v_x_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(lean_object* v___x_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v___x_4615_; lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4626_; 
v___x_4615_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__0___redArg(v___x_4609_, v___y_4611_);
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4626_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4626_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
uint8_t v___x_4620_; 
v___x_4620_ = l_Lean_Expr_hasSyntheticSorry(v_a_4616_);
if (v___x_4620_ == 0)
{
lean_object* v___x_4621_; 
lean_del_object(v___x_4618_);
v___x_4621_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go(v_a_4616_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
return v___x_4621_;
}
else
{
lean_object* v___x_4622_; lean_object* v___x_4624_; 
lean_dec(v_a_4616_);
v___x_4622_ = lean_box(0);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4622_);
v___x_4624_ = v___x_4618_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed(lean_object* v___x_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0(v___x_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(lean_object* v_mvarId_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v___x_4640_; lean_object* v___f_4641_; lean_object* v___x_4642_; 
lean_inc(v_mvarId_4634_);
v___x_4640_ = l_Lean_mkMVar(v_mvarId_4634_);
v___f_4641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4641_, 0, v___x_4640_);
v___x_4642_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_spec__1___redArg(v_mvarId_4634_, v___f_4641_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f___boxed(lean_object* v_mvarId_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(lean_object* v_mvarId_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg___boxed(lean_object* v_mvarId_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___redArg(v_mvarId_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec_ref(v_a_4658_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(lean_object* v_mvarId_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4664_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback___boxed(lean_object* v_mvarId_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_fallback(v_mvarId_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_zero_4690_; uint8_t v_isZero_4691_; 
v_zero_4690_ = lean_unsigned_to_nat(0u);
v_isZero_4691_ = lean_nat_dec_eq(v_a_4688_, v_zero_4690_);
if (v_isZero_4691_ == 0)
{
if (lean_obj_tag(v_a_4689_) == 6)
{
lean_object* v_body_4692_; lean_object* v_one_4693_; lean_object* v_n_4694_; 
v_body_4692_ = lean_ctor_get(v_a_4689_, 2);
v_one_4693_ = lean_unsigned_to_nat(1u);
v_n_4694_ = lean_nat_sub(v_a_4688_, v_one_4693_);
lean_dec(v_a_4688_);
v_a_4688_ = v_n_4694_;
v_a_4689_ = v_body_4692_;
goto _start;
}
else
{
lean_dec(v_a_4688_);
lean_inc_ref(v_a_4689_);
return v_a_4689_;
}
}
else
{
lean_dec(v_a_4688_);
lean_inc_ref(v_a_4689_);
return v_a_4689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody___boxed(lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v_a_4696_, v_a_4697_);
lean_dec_ref(v_a_4697_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(lean_object* v_mvarId_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; lean_object* v_mctx_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4702_ = lean_st_ref_get(v___y_4700_);
v_mctx_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc_ref(v_mctx_4703_);
lean_dec(v___x_4702_);
v___x_4704_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_4703_, v_mvarId_4699_);
lean_dec_ref(v_mctx_4703_);
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg___boxed(lean_object* v_mvarId_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec(v_mvarId_4706_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(lean_object* v_mvarId_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4710_, v___y_4717_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___boxed(lean_object* v_mvarId_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1(v_mvarId_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec(v_mvarId_4722_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(lean_object* v_mvarId_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v___x_4737_; lean_object* v_mctx_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4737_ = lean_st_ref_get(v___y_4735_);
v_mctx_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc_ref(v_mctx_4738_);
lean_dec(v___x_4737_);
v___x_4739_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_4738_, v_mvarId_4734_);
lean_dec_ref(v_mctx_4738_);
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg___boxed(lean_object* v_mvarId_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4741_, v___y_4742_);
lean_dec(v___y_4742_);
lean_dec(v_mvarId_4741_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(lean_object* v_mvarId_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4745_, v___y_4752_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___boxed(lean_object* v_mvarId_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4(v_mvarId_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec(v_mvarId_4757_);
return v_res_4768_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(lean_object* v___x_4769_, lean_object* v_x_4770_){
_start:
{
if (lean_obj_tag(v_x_4770_) == 0)
{
uint8_t v___x_4771_; 
v___x_4771_ = 1;
return v___x_4771_;
}
else
{
lean_object* v_head_4772_; lean_object* v_tail_4773_; lean_object* v_fst_4774_; lean_object* v_snd_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; 
v_head_4772_ = lean_ctor_get(v_x_4770_, 0);
v_tail_4773_ = lean_ctor_get(v_x_4770_, 1);
v_fst_4774_ = lean_ctor_get(v_head_4772_, 0);
v_snd_4775_ = lean_ctor_get(v_head_4772_, 1);
v___x_4776_ = lean_unsigned_to_nat(1u);
v___x_4777_ = lean_nat_sub(v___x_4769_, v___x_4776_);
v___x_4778_ = lean_nat_sub(v___x_4777_, v_snd_4775_);
lean_dec(v___x_4777_);
v___x_4779_ = l_Lean_mkBVar(v___x_4778_);
v___x_4780_ = lean_expr_eqv(v_fst_4774_, v___x_4779_);
lean_dec_ref(v___x_4779_);
if (v___x_4780_ == 0)
{
return v___x_4780_;
}
else
{
v_x_4770_ = v_tail_4773_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0___boxed(lean_object* v___x_4782_, lean_object* v_x_4783_){
_start:
{
uint8_t v_res_4784_; lean_object* v_r_4785_; 
v_res_4784_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4782_, v_x_4783_);
lean_dec(v_x_4783_);
lean_dec(v___x_4782_);
v_r_4785_ = lean_box(v_res_4784_);
return v_r_4785_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(lean_object* v_k_4786_, lean_object* v_t_4787_){
_start:
{
if (lean_obj_tag(v_t_4787_) == 0)
{
lean_object* v_k_4788_; lean_object* v_l_4789_; lean_object* v_r_4790_; uint8_t v___x_4791_; 
v_k_4788_ = lean_ctor_get(v_t_4787_, 1);
v_l_4789_ = lean_ctor_get(v_t_4787_, 3);
v_r_4790_ = lean_ctor_get(v_t_4787_, 4);
v___x_4791_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4786_, v_k_4788_);
switch(v___x_4791_)
{
case 0:
{
v_t_4787_ = v_l_4789_;
goto _start;
}
case 1:
{
uint8_t v___x_4793_; 
v___x_4793_ = 1;
return v___x_4793_;
}
default: 
{
v_t_4787_ = v_r_4790_;
goto _start;
}
}
}
else
{
uint8_t v___x_4795_; 
v___x_4795_ = 0;
return v___x_4795_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg___boxed(lean_object* v_k_4796_, lean_object* v_t_4797_){
_start:
{
uint8_t v_res_4798_; lean_object* v_r_4799_; 
v_res_4798_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4796_, v_t_4797_);
lean_dec(v_t_4797_);
lean_dec(v_k_4796_);
v_r_4799_ = lean_box(v_res_4798_);
return v_r_4799_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(lean_object* v_a_4800_, lean_object* v_as_4801_, size_t v_i_4802_, size_t v_stop_4803_){
_start:
{
uint8_t v___x_4804_; 
v___x_4804_ = lean_usize_dec_eq(v_i_4802_, v_stop_4803_);
if (v___x_4804_ == 0)
{
lean_object* v_fvars_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v_fvars_4805_ = lean_ctor_get(v_a_4800_, 0);
v___x_4806_ = lean_array_uget_borrowed(v_as_4801_, v_i_4802_);
v___x_4807_ = l_Lean_Expr_fvarId_x21(v___x_4806_);
v___x_4808_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v___x_4807_, v_fvars_4805_);
lean_dec(v___x_4807_);
if (v___x_4808_ == 0)
{
size_t v___x_4809_; size_t v___x_4810_; 
v___x_4809_ = ((size_t)1ULL);
v___x_4810_ = lean_usize_add(v_i_4802_, v___x_4809_);
v_i_4802_ = v___x_4810_;
goto _start;
}
else
{
return v___x_4808_;
}
}
else
{
uint8_t v___x_4812_; 
v___x_4812_ = 0;
return v___x_4812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3___boxed(lean_object* v_a_4813_, lean_object* v_as_4814_, lean_object* v_i_4815_, lean_object* v_stop_4816_){
_start:
{
size_t v_i_boxed_4817_; size_t v_stop_boxed_4818_; uint8_t v_res_4819_; lean_object* v_r_4820_; 
v_i_boxed_4817_ = lean_unbox_usize(v_i_4815_);
lean_dec(v_i_4815_);
v_stop_boxed_4818_ = lean_unbox_usize(v_stop_4816_);
lean_dec(v_stop_4816_);
v_res_4819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4813_, v_as_4814_, v_i_boxed_4817_, v_stop_boxed_4818_);
lean_dec_ref(v_as_4814_);
lean_dec_ref(v_a_4813_);
v_r_4820_ = lean_box(v_res_4819_);
return v_r_4820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_4821_; lean_object* v_dummy_4822_; 
v___x_4821_ = lean_box(0);
v_dummy_4822_ = l_Lean_Expr_sort___override(v___x_4821_);
return v_dummy_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_mvarId_4823_, lean_object* v_proof_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_p_4836_; lean_object* v_proof_4839_; lean_object* v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v___y_4924_; lean_object* v___y_4925_; lean_object* v___x_4962_; 
v_proof_4839_ = l_Lean_Expr_headBeta(v_proof_4824_);
v___x_4962_ = l_Lean_Expr_getAppFn(v_proof_4839_);
if (lean_obj_tag(v___x_4962_) == 2)
{
lean_object* v_mvarId_4963_; lean_object* v___x_4964_; 
v_mvarId_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_mvarId_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__4___redArg(v_mvarId_4963_, v_a_4831_);
lean_dec(v_mvarId_4963_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
if (lean_obj_tag(v_a_4965_) == 1)
{
lean_object* v_val_4966_; lean_object* v_dummy_4967_; lean_object* v_nargs_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v_val_4966_ = lean_ctor_get(v_a_4965_, 0);
lean_inc(v_val_4966_);
lean_dec_ref_known(v_a_4965_, 1);
v_dummy_4967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4968_ = l_Lean_Expr_getAppNumArgs(v_proof_4839_);
lean_inc(v_nargs_4968_);
v___x_4969_ = lean_mk_array(v_nargs_4968_, v_dummy_4967_);
v___x_4970_ = lean_unsigned_to_nat(1u);
v___x_4971_ = lean_nat_sub(v_nargs_4968_, v___x_4970_);
lean_dec(v_nargs_4968_);
v___x_4972_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_proof_4839_, v___x_4969_, v___x_4971_);
v___x_4973_ = l_Lean_Expr_beta(v_val_4966_, v___x_4972_);
v_proof_4824_ = v___x_4973_;
goto _start;
}
else
{
lean_dec(v_a_4965_);
v___y_4917_ = v_a_4825_;
v___y_4918_ = v_a_4826_;
v___y_4919_ = v_a_4827_;
v___y_4920_ = v_a_4828_;
v___y_4921_ = v_a_4829_;
v___y_4922_ = v_a_4830_;
v___y_4923_ = v_a_4831_;
v___y_4924_ = v_a_4832_;
v___y_4925_ = v_a_4833_;
goto v___jp_4916_;
}
}
else
{
lean_dec_ref(v_proof_4839_);
lean_dec(v_mvarId_4823_);
return v___x_4964_;
}
}
else
{
lean_dec_ref(v___x_4962_);
v___y_4917_ = v_a_4825_;
v___y_4918_ = v_a_4826_;
v___y_4919_ = v_a_4827_;
v___y_4920_ = v_a_4828_;
v___y_4921_ = v_a_4829_;
v___y_4922_ = v_a_4830_;
v___y_4923_ = v_a_4831_;
v___y_4924_ = v_a_4832_;
v___y_4925_ = v_a_4833_;
goto v___jp_4916_;
}
v___jp_4835_:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4837_, 0, v_p_4836_);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
return v___x_4838_;
}
v___jp_4840_:
{
if (lean_obj_tag(v_proof_4839_) == 6)
{
lean_object* v___x_4850_; lean_object* v___x_4851_; uint8_t v___x_4852_; 
v___x_4850_ = l_Lean_Expr_getNumHeadLambdas(v_proof_4839_);
lean_inc(v___x_4850_);
v___x_4851_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_lambdaBody(v___x_4850_, v_proof_4839_);
lean_dec_ref_known(v_proof_4839_, 3);
v___x_4852_ = l_Lean_Expr_hasLooseBVars(v___x_4851_);
if (v___x_4852_ == 0)
{
lean_dec(v___x_4850_);
v_proof_4824_ = v___x_4851_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
v_a_4832_ = v___y_4848_;
v_a_4833_ = v___y_4849_;
goto _start;
}
else
{
lean_object* v___x_4854_; 
v___x_4854_ = l_Lean_Expr_getAppFn(v___x_4851_);
if (lean_obj_tag(v___x_4854_) == 2)
{
lean_object* v_mvarId_4855_; lean_object* v_dummy_4856_; lean_object* v_nargs_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v_mvarId_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_mvarId_4855_);
lean_dec_ref_known(v___x_4854_, 1);
v_dummy_4856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0);
v_nargs_4857_ = l_Lean_Expr_getAppNumArgs(v___x_4851_);
lean_inc(v_nargs_4857_);
v___x_4858_ = lean_mk_array(v_nargs_4857_, v_dummy_4856_);
v___x_4859_ = lean_unsigned_to_nat(1u);
v___x_4860_ = lean_nat_sub(v_nargs_4857_, v___x_4859_);
lean_dec(v_nargs_4857_);
v___x_4861_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_4851_, v___x_4858_, v___x_4860_);
v___x_4862_ = lean_array_get_size(v___x_4861_);
v___x_4863_ = lean_nat_dec_eq(v___x_4862_, v___x_4850_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; 
lean_dec_ref(v___x_4861_);
lean_dec(v_mvarId_4855_);
lean_dec(v___x_4850_);
v___x_4864_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4823_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4864_;
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; 
v___x_4865_ = lean_array_to_list(v___x_4861_);
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = l_List_zipIdxTR___redArg(v___x_4865_, v___x_4866_);
v___x_4868_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__0(v___x_4850_, v___x_4867_);
lean_dec(v___x_4867_);
if (v___x_4868_ == 0)
{
lean_object* v___x_4869_; 
lean_dec(v_mvarId_4855_);
lean_dec(v___x_4850_);
v___x_4869_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4823_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4869_;
}
else
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__1___redArg(v_mvarId_4855_, v___y_4847_);
lean_dec(v_mvarId_4855_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
lean_inc(v_a_4871_);
lean_dec_ref_known(v___x_4870_, 1);
if (lean_obj_tag(v_a_4871_) == 1)
{
lean_object* v_val_4872_; lean_object* v_fvars_4873_; lean_object* v_mvarIdPending_4874_; lean_object* v___x_4875_; uint8_t v___x_4876_; 
v_val_4872_ = lean_ctor_get(v_a_4871_, 0);
lean_inc(v_val_4872_);
lean_dec_ref_known(v_a_4871_, 1);
v_fvars_4873_ = lean_ctor_get(v_val_4872_, 0);
lean_inc_ref(v_fvars_4873_);
v_mvarIdPending_4874_ = lean_ctor_get(v_val_4872_, 1);
lean_inc(v_mvarIdPending_4874_);
lean_dec(v_val_4872_);
v___x_4875_ = lean_array_get_size(v_fvars_4873_);
v___x_4876_ = lean_nat_dec_eq(v___x_4875_, v___x_4850_);
lean_dec(v___x_4850_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; 
lean_dec(v_mvarIdPending_4874_);
lean_dec_ref(v_fvars_4873_);
v___x_4877_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4823_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4877_;
}
else
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = l_Lean_mkMVar(v_mvarIdPending_4874_);
lean_inc_ref(v___x_4878_);
v___x_4879_ = l_Lean_Meta_Grind_getProofInfo(v___x_4878_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4895_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4895_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4895_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
uint8_t v___x_4884_; 
v___x_4884_ = lean_nat_dec_lt(v___x_4866_, v___x_4875_);
if (v___x_4884_ == 0)
{
lean_del_object(v___x_4882_);
lean_dec(v_a_4880_);
lean_dec_ref(v_fvars_4873_);
v_proof_4824_ = v___x_4878_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
v_a_4832_ = v___y_4848_;
v_a_4833_ = v___y_4849_;
goto _start;
}
else
{
if (v___x_4884_ == 0)
{
lean_del_object(v___x_4882_);
lean_dec(v_a_4880_);
lean_dec_ref(v_fvars_4873_);
v_proof_4824_ = v___x_4878_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
v_a_4832_ = v___y_4848_;
v_a_4833_ = v___y_4849_;
goto _start;
}
else
{
size_t v___x_4887_; size_t v___x_4888_; uint8_t v___x_4889_; 
v___x_4887_ = ((size_t)0ULL);
v___x_4888_ = lean_usize_of_nat(v___x_4875_);
v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__3(v_a_4880_, v_fvars_4873_, v___x_4887_, v___x_4888_);
lean_dec_ref(v_fvars_4873_);
lean_dec(v_a_4880_);
if (v___x_4889_ == 0)
{
lean_del_object(v___x_4882_);
v_proof_4824_ = v___x_4878_;
v_a_4825_ = v___y_4841_;
v_a_4826_ = v___y_4842_;
v_a_4827_ = v___y_4843_;
v_a_4828_ = v___y_4844_;
v_a_4829_ = v___y_4845_;
v_a_4830_ = v___y_4846_;
v_a_4831_ = v___y_4847_;
v_a_4832_ = v___y_4848_;
v_a_4833_ = v___y_4849_;
goto _start;
}
else
{
lean_object* v___x_4891_; lean_object* v___x_4893_; 
lean_dec_ref(v___x_4878_);
lean_dec(v_mvarId_4823_);
v___x_4891_ = lean_box(0);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4891_);
v___x_4893_ = v___x_4882_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
lean_dec_ref(v___x_4878_);
lean_dec_ref(v_fvars_4873_);
lean_dec(v_mvarId_4823_);
v_a_4896_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4879_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4879_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
else
{
lean_object* v___x_4904_; 
lean_dec(v_a_4871_);
lean_dec(v___x_4850_);
v___x_4904_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4823_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4904_;
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec(v___x_4850_);
lean_dec(v_mvarId_4823_);
v_a_4905_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4870_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4870_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
}
else
{
lean_object* v___x_4913_; 
lean_dec_ref(v___x_4854_);
lean_dec_ref(v___x_4851_);
lean_dec(v___x_4850_);
v___x_4913_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f(v_mvarId_4823_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4913_;
}
}
}
else
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
lean_dec_ref(v_proof_4839_);
lean_dec(v_mvarId_4823_);
v___x_4914_ = lean_box(0);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
return v___x_4915_;
}
}
v___jp_4916_:
{
lean_object* v___x_4926_; 
lean_inc_ref(v_proof_4839_);
v___x_4926_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4839_, v___y_4923_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4953_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4929_ = v___x_4926_;
v_isShared_4930_ = v_isSharedCheck_4953_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4953_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; uint8_t v___x_4932_; 
v___x_4931_ = l_Lean_Expr_cleanupAnnotations(v_a_4927_);
lean_dec(v_a_4927_);
v___x_4932_ = l_Lean_Expr_isApp(v___x_4931_);
if (v___x_4932_ == 0)
{
lean_dec_ref(v___x_4931_);
lean_del_object(v___x_4929_);
v___y_4841_ = v___y_4917_;
v___y_4842_ = v___y_4918_;
v___y_4843_ = v___y_4919_;
v___y_4844_ = v___y_4920_;
v___y_4845_ = v___y_4921_;
v___y_4846_ = v___y_4922_;
v___y_4847_ = v___y_4923_;
v___y_4848_ = v___y_4924_;
v___y_4849_ = v___y_4925_;
goto v___jp_4840_;
}
else
{
lean_object* v___x_4933_; uint8_t v___x_4934_; 
v___x_4933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4931_);
v___x_4934_ = l_Lean_Expr_isApp(v___x_4933_);
if (v___x_4934_ == 0)
{
lean_dec_ref(v___x_4933_);
lean_dec_ref(v___x_4931_);
lean_del_object(v___x_4929_);
v___y_4841_ = v___y_4917_;
v___y_4842_ = v___y_4918_;
v___y_4843_ = v___y_4919_;
v___y_4844_ = v___y_4920_;
v___y_4845_ = v___y_4921_;
v___y_4846_ = v___y_4922_;
v___y_4847_ = v___y_4923_;
v___y_4848_ = v___y_4924_;
v___y_4849_ = v___y_4925_;
goto v___jp_4840_;
}
else
{
lean_object* v_arg_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
v_arg_4935_ = lean_ctor_get(v___x_4931_, 1);
lean_inc_ref(v_arg_4935_);
lean_dec_ref(v___x_4931_);
v___x_4936_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4933_);
v___x_4937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__1));
v___x_4938_ = l_Lean_Expr_isConstOf(v___x_4936_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; uint8_t v___x_4940_; 
lean_dec_ref(v___x_4933_);
lean_del_object(v___x_4929_);
v___x_4939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__4));
v___x_4940_ = l_Lean_Expr_isConstOf(v___x_4936_, v___x_4939_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProofEager_x3f_go___closed__6));
v___x_4942_ = l_Lean_Expr_isConstOf(v___x_4936_, v___x_4941_);
lean_dec_ref(v___x_4936_);
if (v___x_4942_ == 0)
{
lean_dec_ref(v_arg_4935_);
v___y_4841_ = v___y_4917_;
v___y_4842_ = v___y_4918_;
v___y_4843_ = v___y_4919_;
v___y_4844_ = v___y_4920_;
v___y_4845_ = v___y_4921_;
v___y_4846_ = v___y_4922_;
v___y_4847_ = v___y_4923_;
v___y_4848_ = v___y_4924_;
v___y_4849_ = v___y_4925_;
goto v___jp_4840_;
}
else
{
lean_dec_ref(v_proof_4839_);
lean_dec(v_mvarId_4823_);
v_p_4836_ = v_arg_4935_;
goto v___jp_4835_;
}
}
else
{
lean_dec_ref(v___x_4936_);
lean_dec_ref(v_proof_4839_);
lean_dec(v_mvarId_4823_);
v_p_4836_ = v_arg_4935_;
goto v___jp_4835_;
}
}
else
{
lean_object* v_arg_4943_; uint8_t v___x_4944_; 
lean_dec_ref(v___x_4936_);
lean_dec_ref(v_proof_4839_);
lean_dec(v_mvarId_4823_);
v_arg_4943_ = lean_ctor_get(v___x_4933_, 1);
lean_inc_ref(v_arg_4943_);
lean_dec_ref(v___x_4933_);
v___x_4944_ = l_Lean_Expr_isFalse(v_arg_4943_);
lean_dec_ref(v_arg_4943_);
if (v___x_4944_ == 0)
{
lean_object* v___x_4945_; lean_object* v___x_4947_; 
lean_dec_ref(v_arg_4935_);
v___x_4945_ = lean_box(0);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4945_);
v___x_4947_ = v___x_4929_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
else
{
lean_object* v___x_4949_; lean_object* v___x_4951_; 
v___x_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4949_, 0, v_arg_4935_);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4949_);
v___x_4951_ = v___x_4929_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4949_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec_ref(v_proof_4839_);
lean_dec(v_mvarId_4823_);
v_a_4954_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4926_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4926_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_mvarId_4975_, lean_object* v_proof_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_4975_, v_proof_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
lean_dec(v_a_4985_);
lean_dec_ref(v_a_4984_);
lean_dec(v_a_4983_);
lean_dec_ref(v_a_4982_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
return v_res_4987_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(lean_object* v_00_u03b2_4988_, lean_object* v_k_4989_, lean_object* v_t_4990_){
_start:
{
uint8_t v___x_4991_; 
v___x_4991_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___redArg(v_k_4989_, v_t_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_4992_, lean_object* v_k_4993_, lean_object* v_t_4994_){
_start:
{
uint8_t v_res_4995_; lean_object* v_r_4996_; 
v_res_4995_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_spec__2(v_00_u03b2_4992_, v_k_4993_, v_t_4994_);
lean_dec(v_t_4994_);
lean_dec(v_k_4993_);
v_r_4996_ = lean_box(v_res_4995_);
return v_r_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(lean_object* v_x_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v___x_5008_; 
lean_inc(v___y_5002_);
lean_inc_ref(v___y_5001_);
lean_inc(v___y_5000_);
lean_inc_ref(v___y_4999_);
lean_inc(v___y_4998_);
v___x_5008_ = lean_apply_10(v_x_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, lean_box(0));
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0(v_x_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
lean_dec(v___y_5012_);
lean_dec_ref(v___y_5011_);
lean_dec(v___y_5010_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_mvarId_5021_, lean_object* v_x_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v___f_5033_; lean_object* v___x_5034_; 
lean_inc(v___y_5027_);
lean_inc_ref(v___y_5026_);
lean_inc(v___y_5025_);
lean_inc_ref(v___y_5024_);
lean_inc(v___y_5023_);
v___f_5033_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5033_, 0, v_x_5022_);
lean_closure_set(v___f_5033_, 1, v___y_5023_);
lean_closure_set(v___f_5033_, 2, v___y_5024_);
lean_closure_set(v___f_5033_, 3, v___y_5025_);
lean_closure_set(v___f_5033_, 4, v___y_5026_);
lean_closure_set(v___f_5033_, 5, v___y_5027_);
v___x_5034_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5021_, v___f_5033_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
if (lean_obj_tag(v___x_5034_) == 0)
{
return v___x_5034_;
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_5034_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5034_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_5043_, lean_object* v_x_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5043_, v_x_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_00_u03b1_5056_, lean_object* v_mvarId_5057_, lean_object* v_x_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5057_, v_x_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_00_u03b1_5070_, lean_object* v_mvarId_5071_, lean_object* v_x_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_00_u03b1_5070_, v_mvarId_5071_, v_x_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5078_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v___y_5075_);
lean_dec_ref(v___y_5074_);
lean_dec(v___y_5073_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_5084_, lean_object* v_mvarId_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v___x_5096_; 
lean_inc_ref(v___x_5084_);
v___x_5096_ = l_Lean_Meta_Grind_getProofInfo(v___x_5084_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5109_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5109_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5109_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
uint8_t v_hasSorry_5106_; 
v_hasSorry_5106_ = lean_ctor_get_uint8(v_a_5097_, sizeof(void*)*1);
if (v_hasSorry_5106_ == 0)
{
uint8_t v_hasUnassigned_5107_; 
v_hasUnassigned_5107_ = lean_ctor_get_uint8(v_a_5097_, sizeof(void*)*1 + 1);
lean_dec(v_a_5097_);
if (v_hasUnassigned_5107_ == 0)
{
lean_object* v___x_5108_; 
lean_del_object(v___x_5099_);
v___x_5108_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_mvarId_5085_, v___x_5084_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
return v___x_5108_;
}
else
{
lean_dec(v_mvarId_5085_);
lean_dec_ref(v___x_5084_);
goto v___jp_5101_;
}
}
else
{
lean_dec(v_a_5097_);
lean_dec(v_mvarId_5085_);
lean_dec_ref(v___x_5084_);
goto v___jp_5101_;
}
v___jp_5101_:
{
lean_object* v___x_5102_; lean_object* v___x_5104_; 
v___x_5102_ = lean_box(0);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v___x_5102_);
v___x_5104_ = v___x_5099_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec(v_mvarId_5085_);
lean_dec_ref(v___x_5084_);
v_a_5110_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5096_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5096_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_5118_, lean_object* v_mvarId_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_5118_, v_mvarId_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v___x_5142_; lean_object* v___f_5143_; lean_object* v___x_5144_; 
lean_inc_n(v_mvarId_5131_, 2);
v___x_5142_ = l_Lean_mkMVar(v_mvarId_5131_);
v___f_5143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5143_, 0, v___x_5142_);
lean_closure_set(v___f_5143_, 1, v_mvarId_5131_);
v___x_5144_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5131_, v___f_5143_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
return v_res_5156_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_5178_){
_start:
{
if (lean_obj_tag(v_x_5178_) == 0)
{
uint8_t v___x_5179_; 
v___x_5179_ = 1;
return v___x_5179_;
}
else
{
lean_object* v_head_5180_; lean_object* v_tail_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; 
v_head_5180_ = lean_ctor_get(v_x_5178_, 0);
lean_inc_n(v_head_5180_, 2);
v_tail_5181_ = lean_ctor_get(v_x_5178_, 1);
lean_inc(v_tail_5181_);
lean_dec_ref_known(v_x_5178_, 2);
v___x_5182_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_5183_ = l_Lean_Syntax_isOfKind(v_head_5180_, v___x_5182_);
if (v___x_5183_ == 0)
{
lean_object* v___x_5184_; uint8_t v___x_5185_; 
v___x_5184_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_5180_);
v___x_5185_ = l_Lean_Syntax_isOfKind(v_head_5180_, v___x_5184_);
if (v___x_5185_ == 0)
{
lean_dec(v_head_5180_);
v_x_5178_ = v_tail_5181_;
goto _start;
}
else
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; uint8_t v___x_5190_; 
v___x_5187_ = lean_unsigned_to_nat(1u);
v___x_5188_ = l_Lean_Syntax_getArg(v_head_5180_, v___x_5187_);
lean_dec(v_head_5180_);
v___x_5189_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5190_ = l_Lean_Syntax_isOfKind(v___x_5188_, v___x_5189_);
if (v___x_5190_ == 0)
{
v_x_5178_ = v_tail_5181_;
goto _start;
}
else
{
lean_dec(v_tail_5181_);
return v___x_5183_;
}
}
}
else
{
lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; 
v___x_5192_ = lean_unsigned_to_nat(3u);
v___x_5193_ = l_Lean_Syntax_getArg(v_head_5180_, v___x_5192_);
lean_dec(v_head_5180_);
v___x_5194_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_5195_ = l_Lean_Syntax_isOfKind(v___x_5193_, v___x_5194_);
if (v___x_5195_ == 0)
{
v_x_5178_ = v_tail_5181_;
goto _start;
}
else
{
uint8_t v___x_5197_; 
lean_dec(v_tail_5181_);
v___x_5197_ = 0;
return v___x_5197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_5198_){
_start:
{
uint8_t v_res_5199_; lean_object* v_r_5200_; 
v_res_5199_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_5198_);
v_r_5200_ = lean_box(v_res_5199_);
return v_r_5200_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_5201_){
_start:
{
uint8_t v___x_5202_; 
v___x_5202_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_5201_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_5203_){
_start:
{
uint8_t v_res_5204_; lean_object* v_r_5205_; 
v_res_5204_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_5203_);
v_r_5205_ = lean_box(v_res_5204_);
return v_r_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_5221_, lean_object* v_a_5222_){
_start:
{
if (lean_obj_tag(v_seq_5221_) == 0)
{
lean_object* v_ref_5224_; uint8_t v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v_ref_5224_ = lean_ctor_get(v_a_5222_, 2);
v___x_5225_ = 0;
v___x_5226_ = l_Lean_SourceInfo_fromRef(v_ref_5224_, v___x_5225_);
v___x_5227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_5228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_5226_);
v___x_5229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5226_);
lean_ctor_set(v___x_5229_, 1, v___x_5227_);
v___x_5230_ = l_Lean_Syntax_node1(v___x_5226_, v___x_5228_, v___x_5229_);
v___x_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
return v___x_5231_;
}
else
{
lean_object* v_tail_5232_; 
v_tail_5232_ = lean_ctor_get(v_seq_5221_, 1);
if (lean_obj_tag(v_tail_5232_) == 0)
{
lean_object* v_head_5233_; lean_object* v___x_5234_; 
v_head_5233_ = lean_ctor_get(v_seq_5221_, 0);
lean_inc(v_head_5233_);
lean_dec_ref_known(v_seq_5221_, 2);
v___x_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5234_, 0, v_head_5233_);
return v___x_5234_;
}
else
{
lean_object* v_head_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5257_; 
lean_inc(v_tail_5232_);
v_head_5235_ = lean_ctor_get(v_seq_5221_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_seq_5221_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; 
v_unused_5258_ = lean_ctor_get(v_seq_5221_, 1);
lean_dec(v_unused_5258_);
v___x_5237_ = v_seq_5221_;
v_isShared_5238_ = v_isSharedCheck_5257_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_head_5235_);
lean_dec(v_seq_5221_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5257_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5239_; lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5256_; 
v___x_5239_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_5232_, v_a_5222_);
v_a_5240_ = lean_ctor_get(v___x_5239_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5239_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5242_ = v___x_5239_;
v_isShared_5243_ = v_isSharedCheck_5256_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5239_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5256_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v_ref_5244_; uint8_t v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5250_; 
v_ref_5244_ = lean_ctor_get(v_a_5222_, 2);
v___x_5245_ = 0;
v___x_5246_ = l_Lean_SourceInfo_fromRef(v_ref_5244_, v___x_5245_);
v___x_5247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5246_);
if (v_isShared_5238_ == 0)
{
lean_ctor_set_tag(v___x_5237_, 2);
lean_ctor_set(v___x_5237_, 1, v___x_5248_);
lean_ctor_set(v___x_5237_, 0, v___x_5246_);
v___x_5250_ = v___x_5237_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5246_);
lean_ctor_set(v_reuseFailAlloc_5255_, 1, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
lean_object* v___x_5251_; lean_object* v___x_5253_; 
v___x_5251_ = l_Lean_Syntax_node3(v___x_5246_, v___x_5247_, v_head_5235_, v___x_5250_, v_a_5240_);
if (v_isShared_5243_ == 0)
{
lean_ctor_set(v___x_5242_, 0, v___x_5251_);
v___x_5253_ = v___x_5242_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5251_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5259_, v_a_5260_);
lean_dec_ref(v_a_5260_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5263_, v_a_5264_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_5268_, v_a_5269_, v_a_5270_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_5273_, lean_object* v_seq_5274_, lean_object* v_a_5275_){
_start:
{
if (lean_obj_tag(v_seq_5274_) == 0)
{
lean_object* v___x_5277_; 
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v_cases_5273_);
return v___x_5277_;
}
else
{
lean_object* v___x_5278_; lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5293_; 
v___x_5278_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_5274_, v_a_5275_);
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5281_ = v___x_5278_;
v_isShared_5282_ = v_isSharedCheck_5293_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5278_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5293_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v_ref_5283_; uint8_t v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5291_; 
v_ref_5283_ = lean_ctor_get(v_a_5275_, 2);
v___x_5284_ = 0;
v___x_5285_ = l_Lean_SourceInfo_fromRef(v_ref_5283_, v___x_5284_);
v___x_5286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_5287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_5285_);
v___x_5288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5285_);
lean_ctor_set(v___x_5288_, 1, v___x_5287_);
v___x_5289_ = l_Lean_Syntax_node3(v___x_5285_, v___x_5286_, v_cases_5273_, v___x_5288_, v_a_5279_);
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 0, v___x_5289_);
v___x_5291_ = v___x_5281_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_5294_, lean_object* v_seq_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5294_, v_seq_5295_, v_a_5296_);
lean_dec_ref(v_a_5296_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_5299_, lean_object* v_seq_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v___x_5304_; 
v___x_5304_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5299_, v_seq_5300_, v_a_5301_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_5305_, lean_object* v_seq_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_5305_, v_seq_5306_, v_a_5307_, v_a_5308_);
lean_dec(v_a_5308_);
lean_dec_ref(v_a_5307_);
return v_res_5310_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_5311_, lean_object* v_x_5312_){
_start:
{
if (lean_obj_tag(v_x_5311_) == 0)
{
if (lean_obj_tag(v_x_5312_) == 0)
{
uint8_t v___x_5313_; 
v___x_5313_ = 1;
return v___x_5313_;
}
else
{
uint8_t v___x_5314_; 
v___x_5314_ = 0;
return v___x_5314_;
}
}
else
{
if (lean_obj_tag(v_x_5312_) == 0)
{
uint8_t v___x_5315_; 
v___x_5315_ = 0;
return v___x_5315_;
}
else
{
lean_object* v_head_5316_; lean_object* v_tail_5317_; lean_object* v_head_5318_; lean_object* v_tail_5319_; uint8_t v___x_5320_; 
v_head_5316_ = lean_ctor_get(v_x_5311_, 0);
v_tail_5317_ = lean_ctor_get(v_x_5311_, 1);
v_head_5318_ = lean_ctor_get(v_x_5312_, 0);
v_tail_5319_ = lean_ctor_get(v_x_5312_, 1);
v___x_5320_ = l_Lean_Syntax_structEq(v_head_5316_, v_head_5318_);
if (v___x_5320_ == 0)
{
return v___x_5320_;
}
else
{
v_x_5311_ = v_tail_5317_;
v_x_5312_ = v_tail_5319_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_5322_, lean_object* v_x_5323_){
_start:
{
uint8_t v_res_5324_; lean_object* v_r_5325_; 
v_res_5324_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_5322_, v_x_5323_);
lean_dec(v_x_5323_);
lean_dec(v_x_5322_);
v_r_5325_ = lean_box(v_res_5324_);
return v_r_5325_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_5326_, lean_object* v___x_5327_, lean_object* v_as_5328_, size_t v_i_5329_, size_t v_stop_5330_){
_start:
{
uint8_t v___x_5335_; 
v___x_5335_ = lean_usize_dec_eq(v_i_5329_, v_stop_5330_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; uint8_t v___x_5337_; 
v___x_5336_ = lean_array_uget_borrowed(v_as_5328_, v_i_5329_);
v___x_5337_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_5336_, v_alt_5326_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; uint8_t v___x_5339_; 
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = lean_nat_dec_lt(v___x_5338_, v___x_5327_);
if (v___x_5339_ == 0)
{
goto v___jp_5331_;
}
else
{
return v___x_5339_;
}
}
else
{
goto v___jp_5331_;
}
}
else
{
uint8_t v___x_5340_; 
v___x_5340_ = 0;
return v___x_5340_;
}
v___jp_5331_:
{
size_t v___x_5332_; size_t v___x_5333_; 
v___x_5332_ = ((size_t)1ULL);
v___x_5333_ = lean_usize_add(v_i_5329_, v___x_5332_);
v_i_5329_ = v___x_5333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_5341_, lean_object* v___x_5342_, lean_object* v_as_5343_, lean_object* v_i_5344_, lean_object* v_stop_5345_){
_start:
{
size_t v_i_boxed_5346_; size_t v_stop_boxed_5347_; uint8_t v_res_5348_; lean_object* v_r_5349_; 
v_i_boxed_5346_ = lean_unbox_usize(v_i_5344_);
lean_dec(v_i_5344_);
v_stop_boxed_5347_ = lean_unbox_usize(v_stop_5345_);
lean_dec(v_stop_5345_);
v_res_5348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5341_, v___x_5342_, v_as_5343_, v_i_boxed_5346_, v_stop_boxed_5347_);
lean_dec_ref(v_as_5343_);
lean_dec(v___x_5342_);
lean_dec(v_alt_5341_);
v_r_5349_ = lean_box(v_res_5348_);
return v_r_5349_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_5350_){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; uint8_t v___x_5353_; 
v___x_5351_ = lean_unsigned_to_nat(0u);
v___x_5352_ = lean_array_get_size(v_alts_5350_);
v___x_5353_ = lean_nat_dec_lt(v___x_5351_, v___x_5352_);
if (v___x_5353_ == 0)
{
uint8_t v___x_5354_; 
v___x_5354_ = 1;
return v___x_5354_;
}
else
{
lean_object* v_alt_5355_; uint8_t v___x_5356_; 
v_alt_5355_ = lean_array_fget_borrowed(v_alts_5350_, v___x_5351_);
lean_inc(v_alt_5355_);
v___x_5356_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_5355_);
if (v___x_5356_ == 0)
{
return v___x_5356_;
}
else
{
if (v___x_5353_ == 0)
{
return v___x_5353_;
}
else
{
size_t v___x_5357_; size_t v___x_5358_; uint8_t v___x_5359_; 
v___x_5357_ = ((size_t)0ULL);
v___x_5358_ = lean_usize_of_nat(v___x_5352_);
v___x_5359_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_5355_, v___x_5352_, v_alts_5350_, v___x_5357_, v___x_5358_);
if (v___x_5359_ == 0)
{
return v___x_5353_;
}
else
{
uint8_t v___x_5360_; 
v___x_5360_ = 0;
return v___x_5360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_5361_){
_start:
{
uint8_t v_res_5362_; lean_object* v_r_5363_; 
v_res_5362_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5361_);
lean_dec_ref(v_alts_5361_);
v_r_5363_ = lean_box(v_res_5362_);
return v_r_5363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_5371_){
_start:
{
if (lean_obj_tag(v_alt_5371_) == 1)
{
lean_object* v_tail_5372_; 
v_tail_5372_ = lean_ctor_get(v_alt_5371_, 1);
if (lean_obj_tag(v_tail_5372_) == 0)
{
lean_object* v_head_5373_; lean_object* v___x_5374_; uint8_t v___x_5375_; 
v_head_5373_ = lean_ctor_get(v_alt_5371_, 0);
lean_inc(v_head_5373_);
lean_dec_ref_known(v_alt_5371_, 2);
v___x_5374_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_5375_ = l_Lean_Syntax_isOfKind(v_head_5373_, v___x_5374_);
return v___x_5375_;
}
else
{
uint8_t v___x_5376_; 
lean_dec_ref_known(v_alt_5371_, 2);
v___x_5376_ = 0;
return v___x_5376_;
}
}
else
{
uint8_t v___x_5377_; 
lean_dec(v_alt_5371_);
v___x_5377_ = 0;
return v___x_5377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_5378_){
_start:
{
uint8_t v_res_5379_; lean_object* v_r_5380_; 
v_res_5379_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_5378_);
v_r_5380_ = lean_box(v_res_5379_);
return v_r_5380_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_5381_, lean_object* v_x_5382_, lean_object* v___y_5383_){
_start:
{
if (lean_obj_tag(v_x_5381_) == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5385_ = l_List_reverse___redArg(v_x_5382_);
v___x_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5385_);
return v___x_5386_;
}
else
{
lean_object* v_head_5387_; lean_object* v_tail_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5406_; 
v_head_5387_ = lean_ctor_get(v_x_5381_, 0);
v_tail_5388_ = lean_ctor_get(v_x_5381_, 1);
v_isSharedCheck_5406_ = !lean_is_exclusive(v_x_5381_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5390_ = v_x_5381_;
v_isShared_5391_ = v_isSharedCheck_5406_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_tail_5388_);
lean_inc(v_head_5387_);
lean_dec(v_x_5381_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5406_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5392_; 
v___x_5392_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_5387_, v___y_5383_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; lean_object* v___x_5395_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
lean_inc(v_a_5393_);
lean_dec_ref_known(v___x_5392_, 1);
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 1, v_x_5382_);
lean_ctor_set(v___x_5390_, 0, v_a_5393_);
v___x_5395_ = v___x_5390_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5393_);
lean_ctor_set(v_reuseFailAlloc_5397_, 1, v_x_5382_);
v___x_5395_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
v_x_5381_ = v_tail_5388_;
v_x_5382_ = v___x_5395_;
goto _start;
}
}
else
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5405_; 
lean_del_object(v___x_5390_);
lean_dec(v_tail_5388_);
lean_dec(v_x_5382_);
v_a_5398_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5400_ = v___x_5392_;
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5392_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5403_; 
if (v_isShared_5401_ == 0)
{
v___x_5403_ = v___x_5400_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5398_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_5407_, lean_object* v_x_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5407_, v_x_5408_, v___y_5409_);
lean_dec_ref(v___y_5409_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_5412_, lean_object* v_alts_5413_, uint8_t v_compress_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_){
_start:
{
lean_object* v_seq_5419_; 
if (v_compress_5414_ == 0)
{
goto v___jp_5422_;
}
else
{
uint8_t v___x_5432_; 
v___x_5432_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_5413_);
if (v___x_5432_ == 0)
{
goto v___jp_5422_;
}
else
{
lean_object* v___x_5433_; lean_object* v___x_5434_; uint8_t v___x_5435_; 
v___x_5433_ = lean_unsigned_to_nat(0u);
v___x_5434_ = lean_array_get_size(v_alts_5413_);
v___x_5435_ = lean_nat_dec_lt(v___x_5433_, v___x_5434_);
if (v___x_5435_ == 0)
{
lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
lean_dec_ref(v_alts_5413_);
v___x_5436_ = lean_box(0);
v___x_5437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5437_, 0, v_cases_5412_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
v___x_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5438_, 0, v___x_5437_);
return v___x_5438_;
}
else
{
lean_object* v___x_5439_; lean_object* v_firstAlt_5440_; uint8_t v___x_5441_; 
v___x_5439_ = lean_box(0);
v_firstAlt_5440_ = lean_array_get(v___x_5439_, v_alts_5413_, v___x_5433_);
lean_dec_ref(v_alts_5413_);
lean_inc(v_firstAlt_5440_);
v___x_5441_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_5440_);
if (v___x_5441_ == 0)
{
lean_object* v___x_5442_; lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5451_; 
v___x_5442_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_5412_, v_firstAlt_5440_, v_a_5415_);
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5445_ = v___x_5442_;
v_isShared_5446_ = v_isSharedCheck_5451_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5442_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5451_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5447_; lean_object* v___x_5449_; 
v___x_5447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5447_, 0, v_a_5443_);
lean_ctor_set(v___x_5447_, 1, v___x_5439_);
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 0, v___x_5447_);
v___x_5449_ = v___x_5445_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
else
{
lean_object* v___x_5452_; 
lean_dec(v_cases_5412_);
v___x_5452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5452_, 0, v_firstAlt_5440_);
return v___x_5452_;
}
}
}
}
v___jp_5418_:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5420_, 0, v_cases_5412_);
lean_ctor_set(v___x_5420_, 1, v_seq_5419_);
v___x_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5421_, 0, v___x_5420_);
return v___x_5421_;
}
v___jp_5422_:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; uint8_t v___x_5425_; 
v___x_5423_ = lean_array_get_size(v_alts_5413_);
v___x_5424_ = lean_unsigned_to_nat(1u);
v___x_5425_ = lean_nat_dec_eq(v___x_5423_, v___x_5424_);
if (v___x_5425_ == 0)
{
lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5426_ = lean_array_to_list(v_alts_5413_);
v___x_5427_ = lean_box(0);
v___x_5428_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_5426_, v___x_5427_, v_a_5415_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref_known(v___x_5428_, 1);
v_seq_5419_ = v_a_5429_;
goto v___jp_5418_;
}
else
{
lean_dec(v_cases_5412_);
return v___x_5428_;
}
}
else
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = lean_unsigned_to_nat(0u);
v___x_5431_ = lean_array_fget(v_alts_5413_, v___x_5430_);
lean_dec_ref(v_alts_5413_);
v_seq_5419_ = v___x_5431_;
goto v___jp_5418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_5453_, lean_object* v_alts_5454_, lean_object* v_compress_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_){
_start:
{
uint8_t v_compress_boxed_5459_; lean_object* v_res_5460_; 
v_compress_boxed_5459_ = lean_unbox(v_compress_5455_);
v_res_5460_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_5453_, v_alts_5454_, v_compress_boxed_5459_, v_a_5456_, v_a_5457_);
lean_dec(v_a_5457_);
lean_dec_ref(v_a_5456_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_5461_, lean_object* v_x_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5461_, v_x_5462_, v___y_5463_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_5467_, lean_object* v_x_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_5467_, v_x_5468_, v___y_5469_, v___y_5470_);
lean_dec(v___y_5470_);
lean_dec_ref(v___y_5469_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_5473_, lean_object* v___y_5474_){
_start:
{
lean_object* v___x_5476_; lean_object* v_env_5477_; uint8_t v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; 
v___x_5476_ = lean_st_ref_get(v___y_5474_);
v_env_5477_ = lean_ctor_get(v___x_5476_, 0);
lean_inc_ref(v_env_5477_);
lean_dec(v___x_5476_);
v___x_5478_ = l_Lean_Meta_isMatcherAppCore(v_env_5477_, v_e_5473_);
v___x_5479_ = lean_box(v___x_5478_);
v___x_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5479_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v_res_5484_; 
v_res_5484_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5481_, v___y_5482_);
lean_dec(v___y_5482_);
lean_dec_ref(v_e_5481_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_){
_start:
{
lean_object* v___x_5497_; 
v___x_5497_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5485_, v___y_5495_);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v_res_5510_; 
v_res_5510_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
lean_dec(v___y_5502_);
lean_dec_ref(v___y_5501_);
lean_dec(v___y_5500_);
lean_dec(v___y_5499_);
lean_dec_ref(v_e_5498_);
return v_res_5510_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___x_5512_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5513_ = l_Lean_stringToMessageData(v___x_5512_);
return v___x_5513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5514_, lean_object* v_c_5515_, lean_object* v_a_5516_, lean_object* v_numCases_5517_, uint8_t v_isRec_5518_, lean_object* v_anchorInfo_x3f_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_){
_start:
{
lean_object* v_mvarIds_5532_; lean_object* v___x_5582_; 
v___x_5582_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5514_, v___y_5520_);
if (lean_obj_tag(v___x_5582_) == 0)
{
lean_object* v_a_5583_; lean_object* v___y_5585_; lean_object* v___x_5637_; uint8_t v___x_5640_; 
v_a_5583_ = lean_ctor_get(v___x_5582_, 0);
lean_inc(v_a_5583_);
lean_dec_ref_known(v___x_5582_, 1);
v___x_5637_ = lean_unsigned_to_nat(1u);
v___x_5640_ = lean_nat_dec_lt(v___x_5637_, v_numCases_5517_);
if (v___x_5640_ == 0)
{
if (v_isRec_5518_ == 0)
{
lean_inc(v_a_5583_);
v___y_5585_ = v_a_5583_;
goto v___jp_5584_;
}
else
{
goto v___jp_5638_;
}
}
else
{
goto v___jp_5638_;
}
v___jp_5584_:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5515_);
lean_inc_ref(v___x_5514_);
v___x_5587_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5514_, v___y_5585_, v_numCases_5517_, v___x_5586_, v___y_5523_, v___y_5526_, v___y_5528_);
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_object* v___x_5588_; 
lean_dec_ref_known(v___x_5587_, 1);
lean_inc_ref(v___x_5514_);
v___x_5588_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5514_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v_toCold_5589_; lean_object* v_options_5590_; uint8_t v_hasTrace_5591_; 
lean_dec_ref_known(v___x_5588_, 1);
v_toCold_5589_ = lean_ctor_get(v___y_5528_, 0);
v_options_5590_ = lean_ctor_get(v_toCold_5589_, 2);
v_hasTrace_5591_ = lean_ctor_get_uint8(v_options_5590_, sizeof(void*)*1);
if (v_hasTrace_5591_ == 0)
{
lean_dec(v_a_5583_);
goto v___jp_5535_;
}
else
{
lean_object* v_inheritedTraceOptions_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; uint8_t v___x_5595_; 
v_inheritedTraceOptions_5592_ = lean_ctor_get(v_toCold_5589_, 11);
v___x_5593_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5594_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5592_, v_options_5590_, v___x_5594_);
if (v___x_5595_ == 0)
{
lean_dec(v_a_5583_);
goto v___jp_5535_;
}
else
{
lean_object* v___x_5596_; 
v___x_5596_ = l_Lean_Meta_Grind_updateLastTag(v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5596_) == 0)
{
lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; 
lean_dec_ref_known(v___x_5596_, 1);
lean_inc_ref(v___x_5514_);
v___x_5597_ = l_Lean_MessageData_ofExpr(v___x_5514_);
v___x_5598_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5597_);
lean_ctor_set(v___x_5599_, 1, v___x_5598_);
v___x_5600_ = l_Nat_reprFast(v_a_5583_);
v___x_5601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5601_, 0, v___x_5600_);
v___x_5602_ = l_Lean_MessageData_ofFormat(v___x_5601_);
v___x_5603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5603_, 0, v___x_5599_);
lean_ctor_set(v___x_5603_, 1, v___x_5602_);
v___x_5604_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5593_, v___x_5603_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5604_) == 0)
{
lean_dec_ref_known(v___x_5604_, 1);
goto v___jp_5535_;
}
else
{
lean_object* v_a_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5612_; 
lean_dec(v_anchorInfo_x3f_5519_);
lean_dec(v_a_5516_);
lean_dec_ref(v_c_5515_);
lean_dec_ref(v___x_5514_);
v_a_5605_ = lean_ctor_get(v___x_5604_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v___x_5604_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5607_ = v___x_5604_;
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_a_5605_);
lean_dec(v___x_5604_);
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
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_dec(v_a_5583_);
lean_dec(v_anchorInfo_x3f_5519_);
lean_dec(v_a_5516_);
lean_dec_ref(v_c_5515_);
lean_dec_ref(v___x_5514_);
v_a_5613_ = lean_ctor_get(v___x_5596_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5596_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5596_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5596_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_dec(v_a_5583_);
lean_dec(v_anchorInfo_x3f_5519_);
lean_dec(v_a_5516_);
lean_dec_ref(v_c_5515_);
lean_dec_ref(v___x_5514_);
v_a_5621_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5588_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5588_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
else
{
lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
lean_dec(v_a_5583_);
lean_dec(v_anchorInfo_x3f_5519_);
lean_dec(v_a_5516_);
lean_dec_ref(v_c_5515_);
lean_dec_ref(v___x_5514_);
v_a_5629_ = lean_ctor_get(v___x_5587_, 0);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5631_ = v___x_5587_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_dec(v___x_5587_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
v___jp_5638_:
{
lean_object* v___x_5639_; 
v___x_5639_ = lean_nat_add(v_a_5583_, v___x_5637_);
v___y_5585_ = v___x_5639_;
goto v___jp_5584_;
}
}
else
{
lean_object* v_a_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5648_; 
lean_dec(v_anchorInfo_x3f_5519_);
lean_dec(v_numCases_5517_);
lean_dec(v_a_5516_);
lean_dec_ref(v_c_5515_);
lean_dec_ref(v___x_5514_);
v_a_5641_ = lean_ctor_get(v___x_5582_, 0);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5582_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5643_ = v___x_5582_;
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_a_5641_);
lean_dec(v___x_5582_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5644_ == 0)
{
v___x_5646_ = v___x_5643_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5641_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
v___jp_5531_:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5533_, 0, v_mvarIds_5532_);
lean_ctor_set(v___x_5533_, 1, v_anchorInfo_x3f_5519_);
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5533_);
return v___x_5534_;
}
v___jp_5535_:
{
lean_object* v___x_5536_; 
v___x_5536_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5514_, v___y_5529_);
if (lean_obj_tag(v_c_5515_) == 1)
{
lean_object* v_e_5537_; lean_object* v_binderType_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; 
lean_dec_ref(v___x_5536_);
lean_dec_ref(v___x_5514_);
v_e_5537_ = lean_ctor_get(v_c_5515_, 0);
lean_inc_ref(v_e_5537_);
lean_dec_ref_known(v_c_5515_, 2);
v_binderType_5538_ = lean_ctor_get(v_e_5537_, 1);
lean_inc_ref(v_binderType_5538_);
lean_dec_ref(v_e_5537_);
v___x_5539_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5538_);
v___x_5540_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5516_, v___x_5539_, v___y_5522_, v___y_5523_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
lean_inc(v_a_5541_);
lean_dec_ref_known(v___x_5540_, 1);
v_mvarIds_5532_ = v_a_5541_;
goto v___jp_5531_;
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
lean_dec(v_anchorInfo_x3f_5519_);
v_a_5542_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5544_ = v___x_5540_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5540_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
else
{
lean_object* v_a_5550_; uint8_t v___x_5551_; 
lean_dec_ref(v_c_5515_);
v_a_5550_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5550_);
lean_dec_ref(v___x_5536_);
v___x_5551_ = lean_unbox(v_a_5550_);
lean_dec(v_a_5550_);
if (v___x_5551_ == 0)
{
lean_object* v___x_5552_; 
v___x_5552_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5514_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5552_) == 0)
{
lean_object* v_a_5553_; lean_object* v___x_5554_; 
v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
lean_inc(v_a_5553_);
lean_dec_ref_known(v___x_5552_, 1);
v___x_5554_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5516_, v_a_5553_, v___y_5522_, v___y_5523_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v_a_5555_; 
v_a_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_a_5555_);
lean_dec_ref_known(v___x_5554_, 1);
v_mvarIds_5532_ = v_a_5555_;
goto v___jp_5531_;
}
else
{
lean_object* v_a_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5563_; 
lean_dec(v_anchorInfo_x3f_5519_);
v_a_5556_ = lean_ctor_get(v___x_5554_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5563_ == 0)
{
v___x_5558_ = v___x_5554_;
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_a_5556_);
lean_dec(v___x_5554_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5561_; 
if (v_isShared_5559_ == 0)
{
v___x_5561_ = v___x_5558_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
v___x_5561_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
return v___x_5561_;
}
}
}
}
else
{
lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5571_; 
lean_dec(v_anchorInfo_x3f_5519_);
lean_dec(v_a_5516_);
v_a_5564_ = lean_ctor_get(v___x_5552_, 0);
v_isSharedCheck_5571_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5571_ == 0)
{
v___x_5566_ = v___x_5552_;
v_isShared_5567_ = v_isSharedCheck_5571_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_dec(v___x_5552_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5571_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5569_; 
if (v_isShared_5567_ == 0)
{
v___x_5569_ = v___x_5566_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
v___x_5569_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
return v___x_5569_;
}
}
}
}
else
{
lean_object* v___x_5572_; 
v___x_5572_ = l_Lean_Meta_Grind_casesMatch(v_a_5516_, v___x_5514_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
lean_inc(v_a_5573_);
lean_dec_ref_known(v___x_5572_, 1);
v_mvarIds_5532_ = v_a_5573_;
goto v___jp_5531_;
}
else
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
lean_dec(v_anchorInfo_x3f_5519_);
v_a_5574_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5572_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5572_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5649_ = _args[0];
lean_object* v_c_5650_ = _args[1];
lean_object* v_a_5651_ = _args[2];
lean_object* v_numCases_5652_ = _args[3];
lean_object* v_isRec_5653_ = _args[4];
lean_object* v_anchorInfo_x3f_5654_ = _args[5];
lean_object* v___y_5655_ = _args[6];
lean_object* v___y_5656_ = _args[7];
lean_object* v___y_5657_ = _args[8];
lean_object* v___y_5658_ = _args[9];
lean_object* v___y_5659_ = _args[10];
lean_object* v___y_5660_ = _args[11];
lean_object* v___y_5661_ = _args[12];
lean_object* v___y_5662_ = _args[13];
lean_object* v___y_5663_ = _args[14];
lean_object* v___y_5664_ = _args[15];
lean_object* v___y_5665_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5666_; lean_object* v_res_5667_; 
v_isRec_boxed_5666_ = lean_unbox(v_isRec_5653_);
v_res_5667_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5649_, v_c_5650_, v_a_5651_, v_numCases_5652_, v_isRec_boxed_5666_, v_anchorInfo_x3f_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec(v___y_5655_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5668_, uint8_t v_trace_5669_, lean_object* v___f_5670_, lean_object* v_c_5671_, lean_object* v_candidates_x3f_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
lean_object* v___x_5683_; lean_object* v___y_5685_; 
v___x_5683_ = lean_st_mk_ref(v_goal_5668_);
if (v_trace_5669_ == 0)
{
lean_object* v___x_5704_; lean_object* v___x_5705_; 
lean_dec(v_candidates_x3f_5672_);
v___x_5704_ = lean_box(0);
lean_inc(v___x_5683_);
v___x_5705_ = lean_apply_12(v___f_5670_, v___x_5704_, v___x_5683_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, lean_box(0));
v___y_5685_ = v___x_5705_;
goto v___jp_5684_;
}
else
{
lean_object* v___x_5706_; 
v___x_5706_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5671_, v_candidates_x3f_5672_, v___x_5683_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_object* v_a_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; 
v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
lean_inc(v_a_5707_);
lean_dec_ref_known(v___x_5706_, 1);
v___x_5708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5708_, 0, v_a_5707_);
lean_inc(v___x_5683_);
v___x_5709_ = lean_apply_12(v___f_5670_, v___x_5708_, v___x_5683_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, lean_box(0));
v___y_5685_ = v___x_5709_;
goto v___jp_5684_;
}
else
{
lean_object* v_a_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5717_; 
lean_dec(v___x_5683_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v___f_5670_);
v_a_5710_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5712_ = v___x_5706_;
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_a_5710_);
lean_dec(v___x_5706_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
if (v_isShared_5713_ == 0)
{
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_a_5710_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
}
v___jp_5684_:
{
if (lean_obj_tag(v___y_5685_) == 0)
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5695_; 
v_a_5686_ = lean_ctor_get(v___y_5685_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___y_5685_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5688_ = v___y_5685_;
v_isShared_5689_ = v_isSharedCheck_5695_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___y_5685_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5695_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5693_; 
v___x_5690_ = lean_st_ref_get(v___x_5683_);
lean_dec(v___x_5683_);
v___x_5691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5691_, 0, v_a_5686_);
lean_ctor_set(v___x_5691_, 1, v___x_5690_);
if (v_isShared_5689_ == 0)
{
lean_ctor_set(v___x_5688_, 0, v___x_5691_);
v___x_5693_ = v___x_5688_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5691_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_dec(v___x_5683_);
v_a_5696_ = lean_ctor_get(v___y_5685_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___y_5685_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___y_5685_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___y_5685_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5718_, lean_object* v_trace_5719_, lean_object* v___f_5720_, lean_object* v_c_5721_, lean_object* v_candidates_x3f_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
uint8_t v_trace_boxed_5733_; lean_object* v_res_5734_; 
v_trace_boxed_5733_ = lean_unbox(v_trace_5719_);
v_res_5734_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5718_, v_trace_boxed_5733_, v___f_5720_, v_c_5721_, v_candidates_x3f_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_);
lean_dec_ref(v_c_5721_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object* v_snd_5735_, lean_object* v_a_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v___x_5747_; 
v___x_5747_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5735_, v___y_5739_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v_a_5748_; lean_object* v___x_5749_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
lean_inc(v_a_5748_);
lean_dec_ref_known(v___x_5747_, 1);
lean_inc(v_a_5736_);
v___x_5749_ = l_Lean_MVarId_getType(v_a_5736_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_);
if (lean_obj_tag(v___x_5749_) == 0)
{
lean_object* v_a_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
lean_inc(v_a_5750_);
lean_dec_ref_known(v___x_5749_, 1);
v___x_5751_ = l_Lean_mkMVar(v_a_5736_);
v___x_5752_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5748_, v___x_5751_, v_a_5750_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_);
return v___x_5752_;
}
else
{
lean_dec(v_a_5748_);
lean_dec(v_a_5736_);
return v___x_5749_;
}
}
else
{
lean_object* v_a_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5760_; 
lean_dec(v_a_5736_);
v_a_5753_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5755_ = v___x_5747_;
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_a_5753_);
lean_dec(v___x_5747_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5758_; 
if (v_isShared_5756_ == 0)
{
v___x_5758_ = v___x_5755_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object* v_snd_5761_, lean_object* v_a_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(v_snd_5761_, v_a_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
lean_dec(v___y_5771_);
lean_dec_ref(v___y_5770_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec(v___y_5763_);
lean_dec_ref(v_snd_5761_);
return v_res_5773_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; 
v___x_5776_ = lean_box(0);
v___x_5777_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__0));
v___x_5778_ = l_Lean_mkConst(v___x_5777_, v___x_5776_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(lean_object* v___x_5779_, lean_object* v_snd_5780_, lean_object* v___x_5781_, lean_object* v_i_5782_, lean_object* v_falseProof_5783_, lean_object* v_seq_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_){
_start:
{
lean_object* v___x_5795_; lean_object* v_congrThms_5796_; lean_object* v_simp_5797_; lean_object* v_symSimp_5798_; lean_object* v_symDSimp_5799_; lean_object* v_lastTag_5800_; lean_object* v_counters_5801_; lean_object* v_splitDiags_5802_; lean_object* v_ematchDiags_5803_; lean_object* v_lawfulEqCmpMap_5804_; lean_object* v_reflCmpMap_5805_; lean_object* v_anchors_5806_; lean_object* v_fvarAnchors_5807_; lean_object* v_instanceMap_5808_; lean_object* v_hoistedDecls_5809_; lean_object* v_proofInfos_5810_; lean_object* v_numBranches_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5864_; 
v___x_5795_ = lean_st_ref_take(v___y_5787_);
v_congrThms_5796_ = lean_ctor_get(v___x_5795_, 0);
v_simp_5797_ = lean_ctor_get(v___x_5795_, 1);
v_symSimp_5798_ = lean_ctor_get(v___x_5795_, 2);
v_symDSimp_5799_ = lean_ctor_get(v___x_5795_, 3);
v_lastTag_5800_ = lean_ctor_get(v___x_5795_, 4);
v_counters_5801_ = lean_ctor_get(v___x_5795_, 5);
v_splitDiags_5802_ = lean_ctor_get(v___x_5795_, 6);
v_ematchDiags_5803_ = lean_ctor_get(v___x_5795_, 7);
v_lawfulEqCmpMap_5804_ = lean_ctor_get(v___x_5795_, 8);
v_reflCmpMap_5805_ = lean_ctor_get(v___x_5795_, 9);
v_anchors_5806_ = lean_ctor_get(v___x_5795_, 10);
v_fvarAnchors_5807_ = lean_ctor_get(v___x_5795_, 11);
v_instanceMap_5808_ = lean_ctor_get(v___x_5795_, 12);
v_hoistedDecls_5809_ = lean_ctor_get(v___x_5795_, 13);
v_proofInfos_5810_ = lean_ctor_get(v___x_5795_, 14);
v_numBranches_5811_ = lean_ctor_get(v___x_5795_, 15);
v_isSharedCheck_5864_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5864_ == 0)
{
v___x_5813_ = v___x_5795_;
v_isShared_5814_ = v_isSharedCheck_5864_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_numBranches_5811_);
lean_inc(v_proofInfos_5810_);
lean_inc(v_hoistedDecls_5809_);
lean_inc(v_instanceMap_5808_);
lean_inc(v_fvarAnchors_5807_);
lean_inc(v_anchors_5806_);
lean_inc(v_reflCmpMap_5805_);
lean_inc(v_lawfulEqCmpMap_5804_);
lean_inc(v_ematchDiags_5803_);
lean_inc(v_splitDiags_5802_);
lean_inc(v_counters_5801_);
lean_inc(v_lastTag_5800_);
lean_inc(v_symDSimp_5799_);
lean_inc(v_symSimp_5798_);
lean_inc(v_simp_5797_);
lean_inc(v_congrThms_5796_);
lean_dec(v___x_5795_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5864_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5820_; 
v___x_5815_ = lean_unsigned_to_nat(1u);
v___x_5816_ = lean_nat_sub(v___x_5779_, v___x_5815_);
v___x_5817_ = lean_nat_sub(v___x_5816_, v_i_5782_);
lean_dec(v___x_5816_);
v___x_5818_ = lean_nat_sub(v_numBranches_5811_, v___x_5817_);
lean_dec(v___x_5817_);
lean_dec(v_numBranches_5811_);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 15, v___x_5818_);
v___x_5820_ = v___x_5813_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_congrThms_5796_);
lean_ctor_set(v_reuseFailAlloc_5863_, 1, v_simp_5797_);
lean_ctor_set(v_reuseFailAlloc_5863_, 2, v_symSimp_5798_);
lean_ctor_set(v_reuseFailAlloc_5863_, 3, v_symDSimp_5799_);
lean_ctor_set(v_reuseFailAlloc_5863_, 4, v_lastTag_5800_);
lean_ctor_set(v_reuseFailAlloc_5863_, 5, v_counters_5801_);
lean_ctor_set(v_reuseFailAlloc_5863_, 6, v_splitDiags_5802_);
lean_ctor_set(v_reuseFailAlloc_5863_, 7, v_ematchDiags_5803_);
lean_ctor_set(v_reuseFailAlloc_5863_, 8, v_lawfulEqCmpMap_5804_);
lean_ctor_set(v_reuseFailAlloc_5863_, 9, v_reflCmpMap_5805_);
lean_ctor_set(v_reuseFailAlloc_5863_, 10, v_anchors_5806_);
lean_ctor_set(v_reuseFailAlloc_5863_, 11, v_fvarAnchors_5807_);
lean_ctor_set(v_reuseFailAlloc_5863_, 12, v_instanceMap_5808_);
lean_ctor_set(v_reuseFailAlloc_5863_, 13, v_hoistedDecls_5809_);
lean_ctor_set(v_reuseFailAlloc_5863_, 14, v_proofInfos_5810_);
lean_ctor_set(v_reuseFailAlloc_5863_, 15, v___x_5818_);
v___x_5820_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = lean_st_ref_put(v___y_5787_, v___x_5820_);
v___x_5822_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5780_, v___y_5787_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v_mvarId_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
lean_inc(v_a_5823_);
lean_dec_ref_known(v___x_5822_, 1);
v_mvarId_5824_ = lean_ctor_get(v_snd_5780_, 1);
lean_inc(v_mvarId_5824_);
lean_dec_ref(v_snd_5780_);
v___x_5825_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_5826_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkHoistedDecls___boxed), 13, 3);
lean_closure_set(v___x_5826_, 0, v_a_5823_);
lean_closure_set(v___x_5826_, 1, v_falseProof_5783_);
lean_closure_set(v___x_5826_, 2, v___x_5825_);
v___x_5827_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_5824_, v___x_5826_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5827_) == 0)
{
lean_object* v_a_5828_; lean_object* v___x_5829_; 
v_a_5828_ = lean_ctor_get(v___x_5827_, 0);
lean_inc(v_a_5828_);
lean_dec_ref_known(v___x_5827_, 1);
v___x_5829_ = l_Lean_MVarId_assignFalseProof(v___x_5781_, v_a_5828_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5829_) == 0)
{
lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5837_; 
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5837_ == 0)
{
lean_object* v_unused_5838_; 
v_unused_5838_ = lean_ctor_get(v___x_5829_, 0);
lean_dec(v_unused_5838_);
v___x_5831_ = v___x_5829_;
v_isShared_5832_ = v_isSharedCheck_5837_;
goto v_resetjp_5830_;
}
else
{
lean_dec(v___x_5829_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5837_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5833_; lean_object* v___x_5835_; 
v___x_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5833_, 0, v_seq_5784_);
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 0, v___x_5833_);
v___x_5835_ = v___x_5831_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v___x_5833_);
v___x_5835_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
return v___x_5835_;
}
}
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_dec(v_seq_5784_);
v_a_5839_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5829_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5829_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v___x_5844_; 
if (v_isShared_5842_ == 0)
{
v___x_5844_ = v___x_5841_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5839_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
return v___x_5844_;
}
}
}
}
else
{
lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5854_; 
lean_dec(v_seq_5784_);
lean_dec(v___x_5781_);
v_a_5847_ = lean_ctor_get(v___x_5827_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5849_ = v___x_5827_;
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5827_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
if (v_isShared_5850_ == 0)
{
v___x_5852_ = v___x_5849_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_a_5847_);
v___x_5852_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
return v___x_5852_;
}
}
}
}
else
{
lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5862_; 
lean_dec(v_seq_5784_);
lean_dec_ref(v_falseProof_5783_);
lean_dec(v___x_5781_);
lean_dec_ref(v_snd_5780_);
v_a_5855_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5862_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5862_ == 0)
{
v___x_5857_ = v___x_5822_;
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v___x_5822_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5860_; 
if (v_isShared_5858_ == 0)
{
v___x_5860_ = v___x_5857_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
v___x_5860_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5859_;
}
v_reusejp_5859_:
{
return v___x_5860_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___boxed(lean_object* v___x_5865_, lean_object* v_snd_5866_, lean_object* v___x_5867_, lean_object* v_i_5868_, lean_object* v_falseProof_5869_, lean_object* v_seq_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_){
_start:
{
lean_object* v_res_5881_; 
v_res_5881_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5865_, v_snd_5866_, v___x_5867_, v_i_5868_, v_falseProof_5869_, v_seq_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec(v___y_5877_);
lean_dec_ref(v___y_5876_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
lean_dec(v___y_5871_);
lean_dec(v_i_5868_);
lean_dec(v___x_5865_);
return v_res_5881_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v___x_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_){
_start:
{
if (lean_obj_tag(v_a_5883_) == 0)
{
lean_object* v___x_5885_; 
v___x_5885_ = l_List_reverse___redArg(v_a_5884_);
return v___x_5885_;
}
else
{
lean_object* v_head_5886_; lean_object* v_toGoalState_5887_; lean_object* v_tail_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5938_; 
v_head_5886_ = lean_ctor_get(v_a_5883_, 0);
lean_inc(v_head_5886_);
v_toGoalState_5887_ = lean_ctor_get(v_head_5886_, 0);
lean_inc_ref(v_toGoalState_5887_);
v_tail_5888_ = lean_ctor_get(v_a_5883_, 1);
v_isSharedCheck_5938_ = !lean_is_exclusive(v_a_5883_);
if (v_isSharedCheck_5938_ == 0)
{
lean_object* v_unused_5939_; 
v_unused_5939_ = lean_ctor_get(v_a_5883_, 0);
lean_dec(v_unused_5939_);
v___x_5890_ = v_a_5883_;
v_isShared_5891_ = v_isSharedCheck_5938_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_tail_5888_);
lean_dec(v_a_5883_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5938_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v_mvarId_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5936_; 
v_mvarId_5892_ = lean_ctor_get(v_head_5886_, 1);
v_isSharedCheck_5936_ = !lean_is_exclusive(v_head_5886_);
if (v_isSharedCheck_5936_ == 0)
{
lean_object* v_unused_5937_; 
v_unused_5937_ = lean_ctor_get(v_head_5886_, 0);
lean_dec(v_unused_5937_);
v___x_5894_ = v_head_5886_;
v_isShared_5895_ = v_isSharedCheck_5936_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_mvarId_5892_);
lean_dec(v_head_5886_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5936_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v_nextDeclIdx_5896_; lean_object* v_enodeMap_5897_; lean_object* v_exprs_5898_; lean_object* v_parents_5899_; lean_object* v_congrTable_5900_; lean_object* v_appMap_5901_; lean_object* v_indicesFound_5902_; lean_object* v_toProcess_5903_; lean_object* v_internalizing_5904_; uint8_t v_inconsistent_5905_; lean_object* v_nextIdx_5906_; lean_object* v_newRawFacts_5907_; lean_object* v_facts_5908_; lean_object* v_extThms_5909_; lean_object* v_ematch_5910_; lean_object* v_inj_5911_; lean_object* v_split_5912_; lean_object* v_clean_5913_; lean_object* v_sstates_5914_; lean_object* v_goalStack_5915_; uint64_t v_introBase_5916_; lean_object* v_numIntros_5917_; lean_object* v_relevance_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5935_; 
v_nextDeclIdx_5896_ = lean_ctor_get(v_toGoalState_5887_, 0);
v_enodeMap_5897_ = lean_ctor_get(v_toGoalState_5887_, 1);
v_exprs_5898_ = lean_ctor_get(v_toGoalState_5887_, 2);
v_parents_5899_ = lean_ctor_get(v_toGoalState_5887_, 3);
v_congrTable_5900_ = lean_ctor_get(v_toGoalState_5887_, 4);
v_appMap_5901_ = lean_ctor_get(v_toGoalState_5887_, 5);
v_indicesFound_5902_ = lean_ctor_get(v_toGoalState_5887_, 6);
v_toProcess_5903_ = lean_ctor_get(v_toGoalState_5887_, 7);
v_internalizing_5904_ = lean_ctor_get(v_toGoalState_5887_, 8);
v_inconsistent_5905_ = lean_ctor_get_uint8(v_toGoalState_5887_, sizeof(void*)*21 + 8);
v_nextIdx_5906_ = lean_ctor_get(v_toGoalState_5887_, 9);
v_newRawFacts_5907_ = lean_ctor_get(v_toGoalState_5887_, 10);
v_facts_5908_ = lean_ctor_get(v_toGoalState_5887_, 11);
v_extThms_5909_ = lean_ctor_get(v_toGoalState_5887_, 12);
v_ematch_5910_ = lean_ctor_get(v_toGoalState_5887_, 13);
v_inj_5911_ = lean_ctor_get(v_toGoalState_5887_, 14);
v_split_5912_ = lean_ctor_get(v_toGoalState_5887_, 15);
v_clean_5913_ = lean_ctor_get(v_toGoalState_5887_, 16);
v_sstates_5914_ = lean_ctor_get(v_toGoalState_5887_, 17);
v_goalStack_5915_ = lean_ctor_get(v_toGoalState_5887_, 18);
v_introBase_5916_ = lean_ctor_get_uint64(v_toGoalState_5887_, sizeof(void*)*21);
v_numIntros_5917_ = lean_ctor_get(v_toGoalState_5887_, 19);
v_relevance_5918_ = lean_ctor_get(v_toGoalState_5887_, 20);
v_isSharedCheck_5935_ = !lean_is_exclusive(v_toGoalState_5887_);
if (v_isSharedCheck_5935_ == 0)
{
v___x_5920_ = v_toGoalState_5887_;
v_isShared_5921_ = v_isSharedCheck_5935_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_relevance_5918_);
lean_inc(v_numIntros_5917_);
lean_inc(v_goalStack_5915_);
lean_inc(v_sstates_5914_);
lean_inc(v_clean_5913_);
lean_inc(v_split_5912_);
lean_inc(v_inj_5911_);
lean_inc(v_ematch_5910_);
lean_inc(v_extThms_5909_);
lean_inc(v_facts_5908_);
lean_inc(v_newRawFacts_5907_);
lean_inc(v_nextIdx_5906_);
lean_inc(v_internalizing_5904_);
lean_inc(v_toProcess_5903_);
lean_inc(v_indicesFound_5902_);
lean_inc(v_appMap_5901_);
lean_inc(v_congrTable_5900_);
lean_inc(v_parents_5899_);
lean_inc(v_exprs_5898_);
lean_inc(v_enodeMap_5897_);
lean_inc(v_nextDeclIdx_5896_);
lean_dec(v_toGoalState_5887_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5935_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5926_; 
v___x_5922_ = lean_unsigned_to_nat(0u);
v___x_5923_ = lean_array_get_size(v___x_5882_);
v___x_5924_ = l_Array_extract___redArg(v_goalStack_5915_, v___x_5922_, v___x_5923_);
lean_dec_ref(v_goalStack_5915_);
if (v_isShared_5921_ == 0)
{
lean_ctor_set(v___x_5920_, 18, v___x_5924_);
v___x_5926_ = v___x_5920_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_nextDeclIdx_5896_);
lean_ctor_set(v_reuseFailAlloc_5934_, 1, v_enodeMap_5897_);
lean_ctor_set(v_reuseFailAlloc_5934_, 2, v_exprs_5898_);
lean_ctor_set(v_reuseFailAlloc_5934_, 3, v_parents_5899_);
lean_ctor_set(v_reuseFailAlloc_5934_, 4, v_congrTable_5900_);
lean_ctor_set(v_reuseFailAlloc_5934_, 5, v_appMap_5901_);
lean_ctor_set(v_reuseFailAlloc_5934_, 6, v_indicesFound_5902_);
lean_ctor_set(v_reuseFailAlloc_5934_, 7, v_toProcess_5903_);
lean_ctor_set(v_reuseFailAlloc_5934_, 8, v_internalizing_5904_);
lean_ctor_set(v_reuseFailAlloc_5934_, 9, v_nextIdx_5906_);
lean_ctor_set(v_reuseFailAlloc_5934_, 10, v_newRawFacts_5907_);
lean_ctor_set(v_reuseFailAlloc_5934_, 11, v_facts_5908_);
lean_ctor_set(v_reuseFailAlloc_5934_, 12, v_extThms_5909_);
lean_ctor_set(v_reuseFailAlloc_5934_, 13, v_ematch_5910_);
lean_ctor_set(v_reuseFailAlloc_5934_, 14, v_inj_5911_);
lean_ctor_set(v_reuseFailAlloc_5934_, 15, v_split_5912_);
lean_ctor_set(v_reuseFailAlloc_5934_, 16, v_clean_5913_);
lean_ctor_set(v_reuseFailAlloc_5934_, 17, v_sstates_5914_);
lean_ctor_set(v_reuseFailAlloc_5934_, 18, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5934_, 19, v_numIntros_5917_);
lean_ctor_set(v_reuseFailAlloc_5934_, 20, v_relevance_5918_);
lean_ctor_set_uint8(v_reuseFailAlloc_5934_, sizeof(void*)*21 + 8, v_inconsistent_5905_);
lean_ctor_set_uint64(v_reuseFailAlloc_5934_, sizeof(void*)*21, v_introBase_5916_);
v___x_5926_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5928_; 
if (v_isShared_5895_ == 0)
{
lean_ctor_set(v___x_5894_, 0, v___x_5926_);
v___x_5928_ = v___x_5894_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5933_, 1, v_mvarId_5892_);
v___x_5928_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
lean_object* v___x_5930_; 
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 1, v_a_5884_);
lean_ctor_set(v___x_5890_, 0, v___x_5928_);
v___x_5930_ = v___x_5890_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v___x_5928_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_a_5884_);
v___x_5930_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
v_a_5883_ = v_tail_5888_;
v_a_5884_ = v___x_5930_;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v___x_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_){
_start:
{
lean_object* v_res_5943_; 
v_res_5943_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5940_, v_a_5941_, v_a_5942_);
lean_dec_ref(v___x_5940_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(lean_object* v___x_5944_, lean_object* v_gs_5945_){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; 
v___x_5946_ = lean_box(0);
v___x_5947_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v___x_5944_, v_gs_5945_, v___x_5946_);
return v___x_5947_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0___boxed(lean_object* v___x_5948_, lean_object* v_gs_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5948_, v_gs_5949_);
lean_dec_ref(v___x_5948_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5951_, lean_object* v_a_5952_, lean_object* v_goal_5953_, lean_object* v___x_5954_, lean_object* v_snd_5955_, lean_object* v___x_5956_, uint8_t v_stopAtFirstFailure_5957_, lean_object* v___x_5958_, lean_object* v_as_x27_5959_, lean_object* v_b_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_){
_start:
{
if (lean_obj_tag(v_as_x27_5959_) == 0)
{
lean_object* v___x_5971_; 
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v___x_5971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5971_, 0, v_b_5960_);
return v___x_5971_;
}
else
{
lean_object* v_snd_5972_; lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_6253_; 
v_snd_5972_ = lean_ctor_get(v_b_5960_, 1);
v_isSharedCheck_6253_ = !lean_is_exclusive(v_b_5960_);
if (v_isSharedCheck_6253_ == 0)
{
lean_object* v_unused_6254_; 
v_unused_6254_ = lean_ctor_get(v_b_5960_, 0);
lean_dec(v_unused_6254_);
v___x_5974_ = v_b_5960_;
v_isShared_5975_ = v_isSharedCheck_6253_;
goto v_resetjp_5973_;
}
else
{
lean_inc(v_snd_5972_);
lean_dec(v_b_5960_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_6253_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v_snd_5976_; lean_object* v_snd_5977_; lean_object* v_snd_5978_; lean_object* v_head_5979_; lean_object* v_tail_5980_; lean_object* v_fst_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_6251_; 
v_snd_5976_ = lean_ctor_get(v_snd_5972_, 1);
lean_inc(v_snd_5976_);
v_snd_5977_ = lean_ctor_get(v_snd_5976_, 1);
lean_inc(v_snd_5977_);
v_snd_5978_ = lean_ctor_get(v_snd_5977_, 1);
lean_inc(v_snd_5978_);
v_head_5979_ = lean_ctor_get(v_as_x27_5959_, 0);
v_tail_5980_ = lean_ctor_get(v_as_x27_5959_, 1);
v_fst_5981_ = lean_ctor_get(v_snd_5972_, 0);
v_isSharedCheck_6251_ = !lean_is_exclusive(v_snd_5972_);
if (v_isSharedCheck_6251_ == 0)
{
lean_object* v_unused_6252_; 
v_unused_6252_ = lean_ctor_get(v_snd_5972_, 1);
lean_dec(v_unused_6252_);
v___x_5983_ = v_snd_5972_;
v_isShared_5984_ = v_isSharedCheck_6251_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_fst_5981_);
lean_dec(v_snd_5972_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_6251_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v_fst_5985_; lean_object* v___x_5987_; uint8_t v_isShared_5988_; uint8_t v_isSharedCheck_6249_; 
v_fst_5985_ = lean_ctor_get(v_snd_5976_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v_snd_5976_);
if (v_isSharedCheck_6249_ == 0)
{
lean_object* v_unused_6250_; 
v_unused_6250_ = lean_ctor_get(v_snd_5976_, 1);
lean_dec(v_unused_6250_);
v___x_5987_ = v_snd_5976_;
v_isShared_5988_ = v_isSharedCheck_6249_;
goto v_resetjp_5986_;
}
else
{
lean_inc(v_fst_5985_);
lean_dec(v_snd_5976_);
v___x_5987_ = lean_box(0);
v_isShared_5988_ = v_isSharedCheck_6249_;
goto v_resetjp_5986_;
}
v_resetjp_5986_:
{
lean_object* v_fst_5989_; lean_object* v___x_5991_; uint8_t v_isShared_5992_; uint8_t v_isSharedCheck_6247_; 
v_fst_5989_ = lean_ctor_get(v_snd_5977_, 0);
v_isSharedCheck_6247_ = !lean_is_exclusive(v_snd_5977_);
if (v_isSharedCheck_6247_ == 0)
{
lean_object* v_unused_6248_; 
v_unused_6248_ = lean_ctor_get(v_snd_5977_, 1);
lean_dec(v_unused_6248_);
v___x_5991_ = v_snd_5977_;
v_isShared_5992_ = v_isSharedCheck_6247_;
goto v_resetjp_5990_;
}
else
{
lean_inc(v_fst_5989_);
lean_dec(v_snd_5977_);
v___x_5991_ = lean_box(0);
v_isShared_5992_ = v_isSharedCheck_6247_;
goto v_resetjp_5990_;
}
v_resetjp_5990_:
{
lean_object* v_start_5993_; lean_object* v_stop_5994_; lean_object* v_step_5995_; lean_object* v___x_5996_; uint8_t v___x_5997_; 
v_start_5993_ = lean_ctor_get(v_snd_5978_, 0);
v_stop_5994_ = lean_ctor_get(v_snd_5978_, 1);
v_step_5995_ = lean_ctor_get(v_snd_5978_, 2);
v___x_5996_ = lean_box(0);
v___x_5997_ = lean_nat_dec_lt(v_start_5993_, v_stop_5994_);
if (v___x_5997_ == 0)
{
lean_object* v___x_5999_; 
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
if (v_isShared_5992_ == 0)
{
v___x_5999_ = v___x_5991_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_fst_5989_);
lean_ctor_set(v_reuseFailAlloc_6010_, 1, v_snd_5978_);
v___x_5999_ = v_reuseFailAlloc_6010_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
lean_object* v___x_6001_; 
if (v_isShared_5988_ == 0)
{
lean_ctor_set(v___x_5987_, 1, v___x_5999_);
v___x_6001_ = v___x_5987_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_fst_5985_);
lean_ctor_set(v_reuseFailAlloc_6009_, 1, v___x_5999_);
v___x_6001_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
lean_object* v___x_6003_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 1, v___x_6001_);
v___x_6003_ = v___x_5983_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_fst_5981_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v___x_6001_);
v___x_6003_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_object* v___x_6005_; 
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_6003_);
lean_ctor_set(v___x_5974_, 0, v___x_5996_);
v___x_6005_ = v___x_5974_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v___x_6003_);
v___x_6005_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
lean_object* v___x_6006_; 
v___x_6006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
return v___x_6006_;
}
}
}
}
}
else
{
lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6243_; 
lean_inc(v_step_5995_);
lean_inc(v_stop_5994_);
lean_inc(v_start_5993_);
v_isSharedCheck_6243_ = !lean_is_exclusive(v_snd_5978_);
if (v_isSharedCheck_6243_ == 0)
{
lean_object* v_unused_6244_; lean_object* v_unused_6245_; lean_object* v_unused_6246_; 
v_unused_6244_ = lean_ctor_get(v_snd_5978_, 2);
lean_dec(v_unused_6244_);
v_unused_6245_ = lean_ctor_get(v_snd_5978_, 1);
lean_dec(v_unused_6245_);
v_unused_6246_ = lean_ctor_get(v_snd_5978_, 0);
lean_dec(v_unused_6246_);
v___x_6012_ = v_snd_5978_;
v_isShared_6013_ = v_isSharedCheck_6243_;
goto v_resetjp_6011_;
}
else
{
lean_dec(v_snd_5978_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6243_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6014_; lean_object* v___x_6016_; 
v___x_6014_ = lean_nat_add(v_start_5993_, v_step_5995_);
if (v_isShared_6013_ == 0)
{
lean_ctor_set(v___x_6012_, 0, v___x_6014_);
v___x_6016_ = v___x_6012_;
goto v_reusejp_6015_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v___x_6014_);
lean_ctor_set(v_reuseFailAlloc_6242_, 1, v_stop_5994_);
lean_ctor_set(v_reuseFailAlloc_6242_, 2, v_step_5995_);
v___x_6016_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6015_;
}
v_reusejp_6015_:
{
lean_object* v___x_6017_; 
lean_inc_ref(v_kp_5951_);
lean_inc(v___y_5969_);
lean_inc_ref(v___y_5968_);
lean_inc(v___y_5967_);
lean_inc_ref(v___y_5966_);
lean_inc(v___y_5965_);
lean_inc_ref(v___y_5964_);
lean_inc(v___y_5963_);
lean_inc_ref(v___y_5962_);
lean_inc(v___y_5961_);
lean_inc(v_head_5979_);
v___x_6017_ = lean_apply_11(v_kp_5951_, v_head_5979_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, lean_box(0));
if (lean_obj_tag(v___x_6017_) == 0)
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6233_; 
v_a_6018_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6233_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6233_ == 0)
{
v___x_6020_ = v___x_6017_;
v_isShared_6021_ = v_isSharedCheck_6233_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___x_6017_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6233_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
if (lean_obj_tag(v_a_6018_) == 0)
{
lean_object* v_seq_6022_; lean_object* v_ncb_x3f_6024_; lean_object* v_mvarId_6053_; lean_object* v___x_6054_; 
lean_del_object(v___x_6020_);
v_seq_6022_ = lean_ctor_get(v_a_6018_, 0);
lean_inc(v_seq_6022_);
lean_dec_ref_known(v_a_6018_, 1);
v_mvarId_6053_ = lean_ctor_get(v_head_5979_, 1);
lean_inc(v_mvarId_6053_);
v___x_6054_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_6053_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
if (lean_obj_tag(v___x_6054_) == 0)
{
lean_object* v_a_6055_; 
v_a_6055_ = lean_ctor_get(v___x_6054_, 0);
lean_inc(v_a_6055_);
lean_dec_ref_known(v___x_6054_, 1);
if (lean_obj_tag(v_a_6055_) == 1)
{
lean_object* v_val_6056_; lean_object* v___x_6058_; uint8_t v_isShared_6059_; uint8_t v_isSharedCheck_6111_; 
v_val_6056_ = lean_ctor_get(v_a_6055_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v_a_6055_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6058_ = v_a_6055_;
v_isShared_6059_ = v_isSharedCheck_6111_;
goto v_resetjp_6057_;
}
else
{
lean_inc(v_val_6056_);
lean_dec(v_a_6055_);
v___x_6058_ = lean_box(0);
v_isShared_6059_ = v_isSharedCheck_6111_;
goto v_resetjp_6057_;
}
v_resetjp_6057_:
{
lean_object* v___x_6060_; 
lean_inc(v_seq_6022_);
lean_inc_ref(v_goal_5953_);
lean_inc(v_a_5952_);
v___x_6060_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_5952_, v_goal_5953_, v_seq_6022_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
if (lean_obj_tag(v___x_6060_) == 0)
{
lean_object* v_a_6061_; uint8_t v___x_6062_; 
v_a_6061_ = lean_ctor_get(v___x_6060_, 0);
lean_inc(v_a_6061_);
lean_dec_ref_known(v___x_6060_, 1);
v___x_6062_ = lean_unbox(v_a_6061_);
lean_dec(v_a_6061_);
if (v___x_6062_ == 0)
{
if (lean_obj_tag(v_fst_5989_) == 0)
{
lean_object* v___x_6063_; 
v___x_6063_ = l_Lean_Meta_Grind_saveState___redArg(v___y_5963_, v___y_5967_, v___y_5969_);
if (lean_obj_tag(v___x_6063_) == 0)
{
lean_object* v_a_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6069_; 
v_a_6064_ = lean_ctor_get(v___x_6063_, 0);
lean_inc(v_a_6064_);
lean_dec_ref_known(v___x_6063_, 1);
lean_inc(v_seq_6022_);
v___x_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6065_, 0, v_val_6056_);
lean_ctor_set(v___x_6065_, 1, v_seq_6022_);
v___x_6066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6066_, 0, v_start_5993_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6067_, 0, v_a_6064_);
lean_ctor_set(v___x_6067_, 1, v___x_6066_);
if (v_isShared_6059_ == 0)
{
lean_ctor_set(v___x_6058_, 0, v___x_6067_);
v___x_6069_ = v___x_6058_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v___x_6067_);
v___x_6069_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
v_ncb_x3f_6024_ = v___x_6069_;
goto v___jp_6023_;
}
}
else
{
lean_object* v_a_6071_; lean_object* v___x_6073_; uint8_t v_isShared_6074_; uint8_t v_isSharedCheck_6078_; 
lean_del_object(v___x_6058_);
lean_dec(v_val_6056_);
lean_dec(v_seq_6022_);
lean_dec_ref(v___x_6016_);
lean_dec(v_start_5993_);
lean_del_object(v___x_5991_);
lean_del_object(v___x_5987_);
lean_dec(v_fst_5985_);
lean_del_object(v___x_5983_);
lean_dec(v_fst_5981_);
lean_del_object(v___x_5974_);
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v_a_6071_ = lean_ctor_get(v___x_6063_, 0);
v_isSharedCheck_6078_ = !lean_is_exclusive(v___x_6063_);
if (v_isSharedCheck_6078_ == 0)
{
v___x_6073_ = v___x_6063_;
v_isShared_6074_ = v_isSharedCheck_6078_;
goto v_resetjp_6072_;
}
else
{
lean_inc(v_a_6071_);
lean_dec(v___x_6063_);
v___x_6073_ = lean_box(0);
v_isShared_6074_ = v_isSharedCheck_6078_;
goto v_resetjp_6072_;
}
v_resetjp_6072_:
{
lean_object* v___x_6076_; 
if (v_isShared_6074_ == 0)
{
v___x_6076_ = v___x_6073_;
goto v_reusejp_6075_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6071_);
v___x_6076_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6075_;
}
v_reusejp_6075_:
{
return v___x_6076_;
}
}
}
}
else
{
lean_del_object(v___x_6058_);
lean_dec(v_val_6056_);
lean_dec(v_start_5993_);
v_ncb_x3f_6024_ = v_fst_5989_;
goto v___jp_6023_;
}
}
else
{
lean_object* v___x_6079_; 
lean_del_object(v___x_5991_);
lean_del_object(v___x_5987_);
lean_del_object(v___x_5983_);
lean_del_object(v___x_5974_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v___x_6079_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5954_, v_snd_5955_, v___x_5956_, v_start_5993_, v_val_6056_, v_seq_6022_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
lean_dec(v_start_5993_);
if (lean_obj_tag(v___x_6079_) == 0)
{
lean_object* v_a_6080_; lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6094_; 
v_a_6080_ = lean_ctor_get(v___x_6079_, 0);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6082_ = v___x_6079_;
v_isShared_6083_ = v_isSharedCheck_6094_;
goto v_resetjp_6081_;
}
else
{
lean_inc(v_a_6080_);
lean_dec(v___x_6079_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6094_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6085_; 
if (v_isShared_6059_ == 0)
{
lean_ctor_set(v___x_6058_, 0, v_a_6080_);
v___x_6085_ = v___x_6058_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_a_6080_);
v___x_6085_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6091_; 
v___x_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6086_, 0, v_fst_5989_);
lean_ctor_set(v___x_6086_, 1, v___x_6016_);
v___x_6087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6087_, 0, v_fst_5985_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6088_, 0, v_fst_5981_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6085_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
if (v_isShared_6083_ == 0)
{
lean_ctor_set(v___x_6082_, 0, v___x_6089_);
v___x_6091_ = v___x_6082_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6092_; 
v_reuseFailAlloc_6092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6092_, 0, v___x_6089_);
v___x_6091_ = v_reuseFailAlloc_6092_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
return v___x_6091_;
}
}
}
}
else
{
lean_object* v_a_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6102_; 
lean_del_object(v___x_6058_);
lean_dec_ref(v___x_6016_);
lean_dec(v_fst_5989_);
lean_dec(v_fst_5985_);
lean_dec(v_fst_5981_);
v_a_6095_ = lean_ctor_get(v___x_6079_, 0);
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6102_ == 0)
{
v___x_6097_ = v___x_6079_;
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_a_6095_);
lean_dec(v___x_6079_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
lean_object* v___x_6100_; 
if (v_isShared_6098_ == 0)
{
v___x_6100_ = v___x_6097_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v_a_6095_);
v___x_6100_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
return v___x_6100_;
}
}
}
}
}
else
{
lean_object* v_a_6103_; lean_object* v___x_6105_; uint8_t v_isShared_6106_; uint8_t v_isSharedCheck_6110_; 
lean_del_object(v___x_6058_);
lean_dec(v_val_6056_);
lean_dec(v_seq_6022_);
lean_dec_ref(v___x_6016_);
lean_dec(v_start_5993_);
lean_del_object(v___x_5991_);
lean_dec(v_fst_5989_);
lean_del_object(v___x_5987_);
lean_dec(v_fst_5985_);
lean_del_object(v___x_5983_);
lean_dec(v_fst_5981_);
lean_del_object(v___x_5974_);
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v_a_6103_ = lean_ctor_get(v___x_6060_, 0);
v_isSharedCheck_6110_ = !lean_is_exclusive(v___x_6060_);
if (v_isSharedCheck_6110_ == 0)
{
v___x_6105_ = v___x_6060_;
v_isShared_6106_ = v_isSharedCheck_6110_;
goto v_resetjp_6104_;
}
else
{
lean_inc(v_a_6103_);
lean_dec(v___x_6060_);
v___x_6105_ = lean_box(0);
v_isShared_6106_ = v_isSharedCheck_6110_;
goto v_resetjp_6104_;
}
v_resetjp_6104_:
{
lean_object* v___x_6108_; 
if (v_isShared_6106_ == 0)
{
v___x_6108_ = v___x_6105_;
goto v_reusejp_6107_;
}
else
{
lean_object* v_reuseFailAlloc_6109_; 
v_reuseFailAlloc_6109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6109_, 0, v_a_6103_);
v___x_6108_ = v_reuseFailAlloc_6109_;
goto v_reusejp_6107_;
}
v_reusejp_6107_:
{
return v___x_6108_;
}
}
}
}
}
else
{
uint8_t v___x_6112_; 
lean_dec(v_a_6055_);
lean_dec(v_start_5993_);
lean_del_object(v___x_5991_);
lean_del_object(v___x_5987_);
lean_del_object(v___x_5983_);
lean_del_object(v___x_5974_);
v___x_6112_ = l_List_isEmpty___redArg(v_seq_6022_);
if (v___x_6112_ == 0)
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6113_ = lean_array_push(v_fst_5981_, v_seq_6022_);
v___x_6114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6114_, 0, v_fst_5989_);
lean_ctor_set(v___x_6114_, 1, v___x_6016_);
v___x_6115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6115_, 0, v_fst_5985_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
v___x_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6113_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_5996_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v_as_x27_5959_ = v_tail_5980_;
v_b_5960_ = v___x_6117_;
goto _start;
}
else
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; 
lean_dec(v_seq_6022_);
v___x_6119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6119_, 0, v_fst_5989_);
lean_ctor_set(v___x_6119_, 1, v___x_6016_);
v___x_6120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6120_, 0, v_fst_5985_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6121_, 0, v_fst_5981_);
lean_ctor_set(v___x_6121_, 1, v___x_6120_);
v___x_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_5996_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v_as_x27_5959_ = v_tail_5980_;
v_b_5960_ = v___x_6122_;
goto _start;
}
}
}
else
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
lean_dec(v_seq_6022_);
lean_dec_ref(v___x_6016_);
lean_dec(v_start_5993_);
lean_del_object(v___x_5991_);
lean_dec(v_fst_5989_);
lean_del_object(v___x_5987_);
lean_dec(v_fst_5985_);
lean_del_object(v___x_5983_);
lean_dec(v_fst_5981_);
lean_del_object(v___x_5974_);
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v_a_6124_ = lean_ctor_get(v___x_6054_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6054_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6054_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6054_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
v___jp_6023_:
{
uint8_t v___x_6025_; 
v___x_6025_ = l_List_isEmpty___redArg(v_seq_6022_);
if (v___x_6025_ == 0)
{
lean_object* v___x_6026_; lean_object* v___x_6028_; 
v___x_6026_ = lean_array_push(v_fst_5981_, v_seq_6022_);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 1, v___x_6016_);
lean_ctor_set(v___x_5991_, 0, v_ncb_x3f_6024_);
v___x_6028_ = v___x_5991_;
goto v_reusejp_6027_;
}
else
{
lean_object* v_reuseFailAlloc_6039_; 
v_reuseFailAlloc_6039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_ncb_x3f_6024_);
lean_ctor_set(v_reuseFailAlloc_6039_, 1, v___x_6016_);
v___x_6028_ = v_reuseFailAlloc_6039_;
goto v_reusejp_6027_;
}
v_reusejp_6027_:
{
lean_object* v___x_6030_; 
if (v_isShared_5988_ == 0)
{
lean_ctor_set(v___x_5987_, 1, v___x_6028_);
v___x_6030_ = v___x_5987_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_fst_5985_);
lean_ctor_set(v_reuseFailAlloc_6038_, 1, v___x_6028_);
v___x_6030_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
lean_object* v___x_6032_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 1, v___x_6030_);
lean_ctor_set(v___x_5983_, 0, v___x_6026_);
v___x_6032_ = v___x_5983_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6037_; 
v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6026_);
lean_ctor_set(v_reuseFailAlloc_6037_, 1, v___x_6030_);
v___x_6032_ = v_reuseFailAlloc_6037_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
lean_object* v___x_6034_; 
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_6032_);
lean_ctor_set(v___x_5974_, 0, v___x_5996_);
v___x_6034_ = v___x_5974_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6036_, 1, v___x_6032_);
v___x_6034_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
v_as_x27_5959_ = v_tail_5980_;
v_b_5960_ = v___x_6034_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_6041_; 
lean_dec(v_seq_6022_);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 1, v___x_6016_);
lean_ctor_set(v___x_5991_, 0, v_ncb_x3f_6024_);
v___x_6041_ = v___x_5991_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_ncb_x3f_6024_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v___x_6016_);
v___x_6041_ = v_reuseFailAlloc_6052_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
lean_object* v___x_6043_; 
if (v_isShared_5988_ == 0)
{
lean_ctor_set(v___x_5987_, 1, v___x_6041_);
v___x_6043_ = v___x_5987_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_fst_5985_);
lean_ctor_set(v_reuseFailAlloc_6051_, 1, v___x_6041_);
v___x_6043_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
lean_object* v___x_6045_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 1, v___x_6043_);
v___x_6045_ = v___x_5983_;
goto v_reusejp_6044_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_fst_5981_);
lean_ctor_set(v_reuseFailAlloc_6050_, 1, v___x_6043_);
v___x_6045_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6044_;
}
v_reusejp_6044_:
{
lean_object* v___x_6047_; 
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_6045_);
lean_ctor_set(v___x_5974_, 0, v___x_5996_);
v___x_6047_ = v___x_5974_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6049_, 1, v___x_6045_);
v___x_6047_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
v_as_x27_5959_ = v_tail_5980_;
v_b_5960_ = v___x_6047_;
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
lean_dec(v_start_5993_);
if (lean_obj_tag(v_fst_5989_) == 1)
{
lean_object* v_val_6132_; lean_object* v_snd_6133_; lean_object* v_snd_6134_; lean_object* v_fst_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6190_; 
lean_dec_ref_known(v_a_6018_, 1);
lean_del_object(v___x_6020_);
lean_del_object(v___x_5987_);
lean_del_object(v___x_5983_);
lean_del_object(v___x_5974_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v_val_6132_ = lean_ctor_get(v_fst_5989_, 0);
lean_inc(v_val_6132_);
v_snd_6133_ = lean_ctor_get(v_val_6132_, 1);
lean_inc(v_snd_6133_);
v_snd_6134_ = lean_ctor_get(v_snd_6133_, 1);
lean_inc(v_snd_6134_);
v_fst_6135_ = lean_ctor_get(v_val_6132_, 0);
v_isSharedCheck_6190_ = !lean_is_exclusive(v_val_6132_);
if (v_isSharedCheck_6190_ == 0)
{
lean_object* v_unused_6191_; 
v_unused_6191_ = lean_ctor_get(v_val_6132_, 1);
lean_dec(v_unused_6191_);
v___x_6137_ = v_val_6132_;
v_isShared_6138_ = v_isSharedCheck_6190_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_fst_6135_);
lean_dec(v_val_6132_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6190_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v_fst_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6188_; 
v_fst_6139_ = lean_ctor_get(v_snd_6133_, 0);
v_isSharedCheck_6188_ = !lean_is_exclusive(v_snd_6133_);
if (v_isSharedCheck_6188_ == 0)
{
lean_object* v_unused_6189_; 
v_unused_6189_ = lean_ctor_get(v_snd_6133_, 1);
lean_dec(v_unused_6189_);
v___x_6141_ = v_snd_6133_;
v_isShared_6142_ = v_isSharedCheck_6188_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_fst_6139_);
lean_dec(v_snd_6133_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6188_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v_fst_6143_; lean_object* v_snd_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6187_; 
v_fst_6143_ = lean_ctor_get(v_snd_6134_, 0);
v_snd_6144_ = lean_ctor_get(v_snd_6134_, 1);
v_isSharedCheck_6187_ = !lean_is_exclusive(v_snd_6134_);
if (v_isSharedCheck_6187_ == 0)
{
v___x_6146_ = v_snd_6134_;
v_isShared_6147_ = v_isSharedCheck_6187_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_snd_6144_);
lean_inc(v_fst_6143_);
lean_dec(v_snd_6134_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6187_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
lean_object* v___x_6148_; 
v___x_6148_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_fst_6135_, v___y_5963_, v___y_5967_, v___y_5969_);
if (lean_obj_tag(v___x_6148_) == 0)
{
lean_object* v___x_6149_; 
lean_dec_ref_known(v___x_6148_, 1);
v___x_6149_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1(v___x_5954_, v_snd_5955_, v___x_5956_, v_fst_6139_, v_fst_6143_, v_snd_6144_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
lean_dec(v_fst_6139_);
if (lean_obj_tag(v___x_6149_) == 0)
{
lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6170_; 
v_a_6150_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6170_ == 0)
{
v___x_6152_ = v___x_6149_;
v_isShared_6153_ = v_isSharedCheck_6170_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6149_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6170_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6154_; lean_object* v___x_6156_; 
v___x_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6154_, 0, v_a_6150_);
if (v_isShared_6147_ == 0)
{
lean_ctor_set(v___x_6146_, 1, v___x_6016_);
lean_ctor_set(v___x_6146_, 0, v_fst_5989_);
v___x_6156_ = v___x_6146_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_fst_5989_);
lean_ctor_set(v_reuseFailAlloc_6169_, 1, v___x_6016_);
v___x_6156_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
lean_object* v___x_6158_; 
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 1, v___x_6156_);
lean_ctor_set(v___x_6141_, 0, v_fst_5985_);
v___x_6158_ = v___x_6141_;
goto v_reusejp_6157_;
}
else
{
lean_object* v_reuseFailAlloc_6168_; 
v_reuseFailAlloc_6168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6168_, 0, v_fst_5985_);
lean_ctor_set(v_reuseFailAlloc_6168_, 1, v___x_6156_);
v___x_6158_ = v_reuseFailAlloc_6168_;
goto v_reusejp_6157_;
}
v_reusejp_6157_:
{
lean_object* v___x_6160_; 
if (v_isShared_6138_ == 0)
{
lean_ctor_set(v___x_6137_, 1, v___x_6158_);
lean_ctor_set(v___x_6137_, 0, v_fst_5981_);
v___x_6160_ = v___x_6137_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_fst_5981_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v___x_6158_);
v___x_6160_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
lean_object* v___x_6162_; 
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 1, v___x_6160_);
lean_ctor_set(v___x_5991_, 0, v___x_6154_);
v___x_6162_ = v___x_5991_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6154_);
lean_ctor_set(v_reuseFailAlloc_6166_, 1, v___x_6160_);
v___x_6162_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
lean_object* v___x_6164_; 
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 0, v___x_6162_);
v___x_6164_ = v___x_6152_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v___x_6162_);
v___x_6164_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
return v___x_6164_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6171_; lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6178_; 
lean_del_object(v___x_6146_);
lean_del_object(v___x_6141_);
lean_del_object(v___x_6137_);
lean_dec_ref_known(v_fst_5989_, 1);
lean_dec_ref(v___x_6016_);
lean_del_object(v___x_5991_);
lean_dec(v_fst_5985_);
lean_dec(v_fst_5981_);
v_a_6171_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6178_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6178_ == 0)
{
v___x_6173_ = v___x_6149_;
v_isShared_6174_ = v_isSharedCheck_6178_;
goto v_resetjp_6172_;
}
else
{
lean_inc(v_a_6171_);
lean_dec(v___x_6149_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6178_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___x_6176_; 
if (v_isShared_6174_ == 0)
{
v___x_6176_ = v___x_6173_;
goto v_reusejp_6175_;
}
else
{
lean_object* v_reuseFailAlloc_6177_; 
v_reuseFailAlloc_6177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_a_6171_);
v___x_6176_ = v_reuseFailAlloc_6177_;
goto v_reusejp_6175_;
}
v_reusejp_6175_:
{
return v___x_6176_;
}
}
}
}
else
{
lean_object* v_a_6179_; lean_object* v___x_6181_; uint8_t v_isShared_6182_; uint8_t v_isSharedCheck_6186_; 
lean_del_object(v___x_6146_);
lean_dec(v_snd_6144_);
lean_dec(v_fst_6143_);
lean_del_object(v___x_6141_);
lean_dec(v_fst_6139_);
lean_del_object(v___x_6137_);
lean_dec_ref_known(v_fst_5989_, 1);
lean_dec_ref(v___x_6016_);
lean_del_object(v___x_5991_);
lean_dec(v_fst_5985_);
lean_dec(v_fst_5981_);
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
v_a_6179_ = lean_ctor_get(v___x_6148_, 0);
v_isSharedCheck_6186_ = !lean_is_exclusive(v___x_6148_);
if (v_isSharedCheck_6186_ == 0)
{
v___x_6181_ = v___x_6148_;
v_isShared_6182_ = v_isSharedCheck_6186_;
goto v_resetjp_6180_;
}
else
{
lean_inc(v_a_6179_);
lean_dec(v___x_6148_);
v___x_6181_ = lean_box(0);
v_isShared_6182_ = v_isSharedCheck_6186_;
goto v_resetjp_6180_;
}
v_resetjp_6180_:
{
lean_object* v___x_6184_; 
if (v_isShared_6182_ == 0)
{
v___x_6184_ = v___x_6181_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6185_; 
v_reuseFailAlloc_6185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6185_, 0, v_a_6179_);
v___x_6184_ = v_reuseFailAlloc_6185_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
return v___x_6184_;
}
}
}
}
}
}
}
else
{
if (v_stopAtFirstFailure_5957_ == 0)
{
lean_object* v_gs_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6196_; 
lean_del_object(v___x_6020_);
v_gs_6192_ = lean_ctor_get(v_a_6018_, 0);
lean_inc(v_gs_6192_);
lean_dec_ref_known(v_a_6018_, 1);
v___x_6193_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5958_, v_gs_6192_);
v___x_6194_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_5985_, v___x_6193_);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 1, v___x_6016_);
v___x_6196_ = v___x_5991_;
goto v_reusejp_6195_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_fst_5989_);
lean_ctor_set(v_reuseFailAlloc_6207_, 1, v___x_6016_);
v___x_6196_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6195_;
}
v_reusejp_6195_:
{
lean_object* v___x_6198_; 
if (v_isShared_5988_ == 0)
{
lean_ctor_set(v___x_5987_, 1, v___x_6196_);
lean_ctor_set(v___x_5987_, 0, v___x_6194_);
v___x_6198_ = v___x_5987_;
goto v_reusejp_6197_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v___x_6194_);
lean_ctor_set(v_reuseFailAlloc_6206_, 1, v___x_6196_);
v___x_6198_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6197_;
}
v_reusejp_6197_:
{
lean_object* v___x_6200_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 1, v___x_6198_);
v___x_6200_ = v___x_5983_;
goto v_reusejp_6199_;
}
else
{
lean_object* v_reuseFailAlloc_6205_; 
v_reuseFailAlloc_6205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6205_, 0, v_fst_5981_);
lean_ctor_set(v_reuseFailAlloc_6205_, 1, v___x_6198_);
v___x_6200_ = v_reuseFailAlloc_6205_;
goto v_reusejp_6199_;
}
v_reusejp_6199_:
{
lean_object* v___x_6202_; 
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_6200_);
lean_ctor_set(v___x_5974_, 0, v___x_5996_);
v___x_6202_ = v___x_5974_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6204_, 1, v___x_6200_);
v___x_6202_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
v_as_x27_5959_ = v_tail_5980_;
v_b_5960_ = v___x_6202_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_gs_6208_; lean_object* v___x_6210_; uint8_t v_isShared_6211_; uint8_t v_isSharedCheck_6232_; 
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v_gs_6208_ = lean_ctor_get(v_a_6018_, 0);
v_isSharedCheck_6232_ = !lean_is_exclusive(v_a_6018_);
if (v_isSharedCheck_6232_ == 0)
{
v___x_6210_ = v_a_6018_;
v_isShared_6211_ = v_isSharedCheck_6232_;
goto v_resetjp_6209_;
}
else
{
lean_inc(v_gs_6208_);
lean_dec(v_a_6018_);
v___x_6210_ = lean_box(0);
v_isShared_6211_ = v_isSharedCheck_6232_;
goto v_resetjp_6209_;
}
v_resetjp_6209_:
{
lean_object* v___x_6212_; lean_object* v___x_6214_; 
v___x_6212_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__0(v___x_5958_, v_gs_6208_);
if (v_isShared_6211_ == 0)
{
lean_ctor_set(v___x_6210_, 0, v___x_6212_);
v___x_6214_ = v___x_6210_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6231_; 
v_reuseFailAlloc_6231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6231_, 0, v___x_6212_);
v___x_6214_ = v_reuseFailAlloc_6231_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
lean_object* v___x_6215_; lean_object* v___x_6217_; 
v___x_6215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6214_);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 1, v___x_6016_);
v___x_6217_ = v___x_5991_;
goto v_reusejp_6216_;
}
else
{
lean_object* v_reuseFailAlloc_6230_; 
v_reuseFailAlloc_6230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_fst_5989_);
lean_ctor_set(v_reuseFailAlloc_6230_, 1, v___x_6016_);
v___x_6217_ = v_reuseFailAlloc_6230_;
goto v_reusejp_6216_;
}
v_reusejp_6216_:
{
lean_object* v___x_6219_; 
if (v_isShared_5988_ == 0)
{
lean_ctor_set(v___x_5987_, 1, v___x_6217_);
v___x_6219_ = v___x_5987_;
goto v_reusejp_6218_;
}
else
{
lean_object* v_reuseFailAlloc_6229_; 
v_reuseFailAlloc_6229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6229_, 0, v_fst_5985_);
lean_ctor_set(v_reuseFailAlloc_6229_, 1, v___x_6217_);
v___x_6219_ = v_reuseFailAlloc_6229_;
goto v_reusejp_6218_;
}
v_reusejp_6218_:
{
lean_object* v___x_6221_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 1, v___x_6219_);
v___x_6221_ = v___x_5983_;
goto v_reusejp_6220_;
}
else
{
lean_object* v_reuseFailAlloc_6228_; 
v_reuseFailAlloc_6228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_fst_5981_);
lean_ctor_set(v_reuseFailAlloc_6228_, 1, v___x_6219_);
v___x_6221_ = v_reuseFailAlloc_6228_;
goto v_reusejp_6220_;
}
v_reusejp_6220_:
{
lean_object* v___x_6223_; 
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_6221_);
lean_ctor_set(v___x_5974_, 0, v___x_6215_);
v___x_6223_ = v___x_5974_;
goto v_reusejp_6222_;
}
else
{
lean_object* v_reuseFailAlloc_6227_; 
v_reuseFailAlloc_6227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6227_, 0, v___x_6215_);
lean_ctor_set(v_reuseFailAlloc_6227_, 1, v___x_6221_);
v___x_6223_ = v_reuseFailAlloc_6227_;
goto v_reusejp_6222_;
}
v_reusejp_6222_:
{
lean_object* v___x_6225_; 
if (v_isShared_6021_ == 0)
{
lean_ctor_set(v___x_6020_, 0, v___x_6223_);
v___x_6225_ = v___x_6020_;
goto v_reusejp_6224_;
}
else
{
lean_object* v_reuseFailAlloc_6226_; 
v_reuseFailAlloc_6226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6226_, 0, v___x_6223_);
v___x_6225_ = v_reuseFailAlloc_6226_;
goto v_reusejp_6224_;
}
v_reusejp_6224_:
{
return v___x_6225_;
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
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
lean_dec_ref(v___x_6016_);
lean_dec(v_start_5993_);
lean_del_object(v___x_5991_);
lean_dec(v_fst_5989_);
lean_del_object(v___x_5987_);
lean_dec(v_fst_5985_);
lean_del_object(v___x_5983_);
lean_dec(v_fst_5981_);
lean_del_object(v___x_5974_);
lean_dec(v___x_5956_);
lean_dec_ref(v_snd_5955_);
lean_dec_ref(v_goal_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_kp_5951_);
v_a_6234_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v___x_6017_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6017_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
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
lean_object* v_kp_6255_ = _args[0];
lean_object* v_a_6256_ = _args[1];
lean_object* v_goal_6257_ = _args[2];
lean_object* v___x_6258_ = _args[3];
lean_object* v_snd_6259_ = _args[4];
lean_object* v___x_6260_ = _args[5];
lean_object* v_stopAtFirstFailure_6261_ = _args[6];
lean_object* v___x_6262_ = _args[7];
lean_object* v_as_x27_6263_ = _args[8];
lean_object* v_b_6264_ = _args[9];
lean_object* v___y_6265_ = _args[10];
lean_object* v___y_6266_ = _args[11];
lean_object* v___y_6267_ = _args[12];
lean_object* v___y_6268_ = _args[13];
lean_object* v___y_6269_ = _args[14];
lean_object* v___y_6270_ = _args[15];
lean_object* v___y_6271_ = _args[16];
lean_object* v___y_6272_ = _args[17];
lean_object* v___y_6273_ = _args[18];
lean_object* v___y_6274_ = _args[19];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6275_; lean_object* v_res_6276_; 
v_stopAtFirstFailure_boxed_6275_ = lean_unbox(v_stopAtFirstFailure_6261_);
v_res_6276_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6255_, v_a_6256_, v_goal_6257_, v___x_6258_, v_snd_6259_, v___x_6260_, v_stopAtFirstFailure_boxed_6275_, v___x_6262_, v_as_x27_6263_, v_b_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
lean_dec(v___y_6271_);
lean_dec_ref(v___y_6270_);
lean_dec(v___y_6269_);
lean_dec_ref(v___y_6268_);
lean_dec(v___y_6267_);
lean_dec_ref(v___y_6266_);
lean_dec(v___y_6265_);
lean_dec(v_as_x27_6263_);
lean_dec_ref(v___x_6262_);
lean_dec(v___x_6258_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v___x_6277_, lean_object* v_c_6278_, lean_object* v___x_6279_, lean_object* v___x_6280_, lean_object* v___x_6281_, uint64_t v_a_6282_, lean_object* v_a_6283_, lean_object* v_a_6284_){
_start:
{
if (lean_obj_tag(v_a_6283_) == 0)
{
lean_object* v___x_6285_; 
lean_dec_ref(v___x_6281_);
lean_dec(v___x_6280_);
lean_dec_ref(v___x_6279_);
lean_dec_ref(v___x_6277_);
v___x_6285_ = lean_array_to_list(v_a_6284_);
return v___x_6285_;
}
else
{
lean_object* v_split_6286_; lean_object* v_head_6287_; lean_object* v_tail_6288_; lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6340_; 
v_split_6286_ = lean_ctor_get(v___x_6277_, 15);
lean_inc_ref(v_split_6286_);
v_head_6287_ = lean_ctor_get(v_a_6283_, 0);
v_tail_6288_ = lean_ctor_get(v_a_6283_, 1);
v_isSharedCheck_6340_ = !lean_is_exclusive(v_a_6283_);
if (v_isSharedCheck_6340_ == 0)
{
v___x_6290_ = v_a_6283_;
v_isShared_6291_ = v_isSharedCheck_6340_;
goto v_resetjp_6289_;
}
else
{
lean_inc(v_tail_6288_);
lean_inc(v_head_6287_);
lean_dec(v_a_6283_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6340_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v_nextDeclIdx_6292_; lean_object* v_enodeMap_6293_; lean_object* v_exprs_6294_; lean_object* v_parents_6295_; lean_object* v_congrTable_6296_; lean_object* v_appMap_6297_; lean_object* v_indicesFound_6298_; lean_object* v_toProcess_6299_; lean_object* v_internalizing_6300_; uint8_t v_inconsistent_6301_; lean_object* v_nextIdx_6302_; lean_object* v_newRawFacts_6303_; lean_object* v_facts_6304_; lean_object* v_extThms_6305_; lean_object* v_ematch_6306_; lean_object* v_inj_6307_; lean_object* v_clean_6308_; lean_object* v_sstates_6309_; uint64_t v_introBase_6310_; lean_object* v_numIntros_6311_; lean_object* v_relevance_6312_; lean_object* v_candidates_6313_; lean_object* v_added_6314_; lean_object* v_resolved_6315_; lean_object* v_trace_6316_; lean_object* v_lookaheads_6317_; lean_object* v_argPosMap_6318_; lean_object* v_argsAt_6319_; lean_object* v___x_6321_; uint8_t v_isShared_6322_; uint8_t v_isSharedCheck_6339_; 
v_nextDeclIdx_6292_ = lean_ctor_get(v___x_6277_, 0);
v_enodeMap_6293_ = lean_ctor_get(v___x_6277_, 1);
v_exprs_6294_ = lean_ctor_get(v___x_6277_, 2);
v_parents_6295_ = lean_ctor_get(v___x_6277_, 3);
v_congrTable_6296_ = lean_ctor_get(v___x_6277_, 4);
v_appMap_6297_ = lean_ctor_get(v___x_6277_, 5);
v_indicesFound_6298_ = lean_ctor_get(v___x_6277_, 6);
v_toProcess_6299_ = lean_ctor_get(v___x_6277_, 7);
v_internalizing_6300_ = lean_ctor_get(v___x_6277_, 8);
v_inconsistent_6301_ = lean_ctor_get_uint8(v___x_6277_, sizeof(void*)*21 + 8);
v_nextIdx_6302_ = lean_ctor_get(v___x_6277_, 9);
v_newRawFacts_6303_ = lean_ctor_get(v___x_6277_, 10);
v_facts_6304_ = lean_ctor_get(v___x_6277_, 11);
v_extThms_6305_ = lean_ctor_get(v___x_6277_, 12);
v_ematch_6306_ = lean_ctor_get(v___x_6277_, 13);
v_inj_6307_ = lean_ctor_get(v___x_6277_, 14);
v_clean_6308_ = lean_ctor_get(v___x_6277_, 16);
v_sstates_6309_ = lean_ctor_get(v___x_6277_, 17);
v_introBase_6310_ = lean_ctor_get_uint64(v___x_6277_, sizeof(void*)*21);
v_numIntros_6311_ = lean_ctor_get(v___x_6277_, 19);
v_relevance_6312_ = lean_ctor_get(v___x_6277_, 20);
v_candidates_6313_ = lean_ctor_get(v_split_6286_, 0);
v_added_6314_ = lean_ctor_get(v_split_6286_, 1);
v_resolved_6315_ = lean_ctor_get(v_split_6286_, 2);
v_trace_6316_ = lean_ctor_get(v_split_6286_, 3);
v_lookaheads_6317_ = lean_ctor_get(v_split_6286_, 4);
v_argPosMap_6318_ = lean_ctor_get(v_split_6286_, 5);
v_argsAt_6319_ = lean_ctor_get(v_split_6286_, 6);
v_isSharedCheck_6339_ = !lean_is_exclusive(v_split_6286_);
if (v_isSharedCheck_6339_ == 0)
{
v___x_6321_ = v_split_6286_;
v_isShared_6322_ = v_isSharedCheck_6339_;
goto v_resetjp_6320_;
}
else
{
lean_inc(v_argsAt_6319_);
lean_inc(v_argPosMap_6318_);
lean_inc(v_lookaheads_6317_);
lean_inc(v_trace_6316_);
lean_inc(v_resolved_6315_);
lean_inc(v_added_6314_);
lean_inc(v_candidates_6313_);
lean_dec(v_split_6286_);
v___x_6321_ = lean_box(0);
v_isShared_6322_ = v_isSharedCheck_6339_;
goto v_resetjp_6320_;
}
v_resetjp_6320_:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6327_; 
v___x_6323_ = lean_array_get_size(v_a_6284_);
v___x_6324_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_6278_);
lean_inc(v___x_6280_);
lean_inc_ref(v___x_6279_);
v___x_6325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6325_, 0, v___x_6279_);
lean_ctor_set(v___x_6325_, 1, v___x_6323_);
lean_ctor_set(v___x_6325_, 2, v___x_6280_);
lean_ctor_set(v___x_6325_, 3, v___x_6324_);
if (v_isShared_6291_ == 0)
{
lean_ctor_set(v___x_6290_, 1, v_trace_6316_);
lean_ctor_set(v___x_6290_, 0, v___x_6325_);
v___x_6327_ = v___x_6290_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v___x_6325_);
lean_ctor_set(v_reuseFailAlloc_6338_, 1, v_trace_6316_);
v___x_6327_ = v_reuseFailAlloc_6338_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
lean_object* v___x_6329_; 
if (v_isShared_6322_ == 0)
{
lean_ctor_set(v___x_6321_, 3, v___x_6327_);
v___x_6329_ = v___x_6321_;
goto v_reusejp_6328_;
}
else
{
lean_object* v_reuseFailAlloc_6337_; 
v_reuseFailAlloc_6337_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_6337_, 0, v_candidates_6313_);
lean_ctor_set(v_reuseFailAlloc_6337_, 1, v_added_6314_);
lean_ctor_set(v_reuseFailAlloc_6337_, 2, v_resolved_6315_);
lean_ctor_set(v_reuseFailAlloc_6337_, 3, v___x_6327_);
lean_ctor_set(v_reuseFailAlloc_6337_, 4, v_lookaheads_6317_);
lean_ctor_set(v_reuseFailAlloc_6337_, 5, v_argPosMap_6318_);
lean_ctor_set(v_reuseFailAlloc_6337_, 6, v_argsAt_6319_);
v___x_6329_ = v_reuseFailAlloc_6337_;
goto v_reusejp_6328_;
}
v_reusejp_6328_:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; uint64_t v___x_6332_; uint64_t v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
lean_inc_ref(v_relevance_6312_);
lean_inc(v_numIntros_6311_);
lean_inc_ref(v___x_6281_);
lean_inc_ref(v_sstates_6309_);
lean_inc_ref(v_clean_6308_);
lean_inc_ref(v_inj_6307_);
lean_inc_ref(v_ematch_6306_);
lean_inc_ref(v_extThms_6305_);
lean_inc_ref(v_facts_6304_);
lean_inc_ref(v_newRawFacts_6303_);
lean_inc(v_nextIdx_6302_);
lean_inc_ref(v_internalizing_6300_);
lean_inc_ref(v_toProcess_6299_);
lean_inc_ref(v_indicesFound_6298_);
lean_inc_ref(v_appMap_6297_);
lean_inc_ref(v_congrTable_6296_);
lean_inc_ref(v_parents_6295_);
lean_inc_ref(v_exprs_6294_);
lean_inc_ref(v_enodeMap_6293_);
lean_inc(v_nextDeclIdx_6292_);
v___x_6330_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v___x_6330_, 0, v_nextDeclIdx_6292_);
lean_ctor_set(v___x_6330_, 1, v_enodeMap_6293_);
lean_ctor_set(v___x_6330_, 2, v_exprs_6294_);
lean_ctor_set(v___x_6330_, 3, v_parents_6295_);
lean_ctor_set(v___x_6330_, 4, v_congrTable_6296_);
lean_ctor_set(v___x_6330_, 5, v_appMap_6297_);
lean_ctor_set(v___x_6330_, 6, v_indicesFound_6298_);
lean_ctor_set(v___x_6330_, 7, v_toProcess_6299_);
lean_ctor_set(v___x_6330_, 8, v_internalizing_6300_);
lean_ctor_set(v___x_6330_, 9, v_nextIdx_6302_);
lean_ctor_set(v___x_6330_, 10, v_newRawFacts_6303_);
lean_ctor_set(v___x_6330_, 11, v_facts_6304_);
lean_ctor_set(v___x_6330_, 12, v_extThms_6305_);
lean_ctor_set(v___x_6330_, 13, v_ematch_6306_);
lean_ctor_set(v___x_6330_, 14, v_inj_6307_);
lean_ctor_set(v___x_6330_, 15, v___x_6329_);
lean_ctor_set(v___x_6330_, 16, v_clean_6308_);
lean_ctor_set(v___x_6330_, 17, v_sstates_6309_);
lean_ctor_set(v___x_6330_, 18, v___x_6281_);
lean_ctor_set(v___x_6330_, 19, v_numIntros_6311_);
lean_ctor_set(v___x_6330_, 20, v_relevance_6312_);
lean_ctor_set_uint8(v___x_6330_, sizeof(void*)*21 + 8, v_inconsistent_6301_);
lean_ctor_set_uint64(v___x_6330_, sizeof(void*)*21, v_introBase_6310_);
v___x_6331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6331_, 0, v___x_6330_);
lean_ctor_set(v___x_6331_, 1, v_head_6287_);
v___x_6332_ = lean_uint64_of_nat(v___x_6323_);
v___x_6333_ = lean_uint64_mix_hash(v_a_6282_, v___x_6332_);
v___x_6334_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_6331_, v___x_6333_);
v___x_6335_ = lean_array_push(v_a_6284_, v___x_6334_);
v_a_6283_ = v_tail_6288_;
v_a_6284_ = v___x_6335_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v___x_6341_, lean_object* v_c_6342_, lean_object* v___x_6343_, lean_object* v___x_6344_, lean_object* v___x_6345_, lean_object* v_a_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_){
_start:
{
uint64_t v_a_118275__boxed_6349_; lean_object* v_res_6350_; 
v_a_118275__boxed_6349_ = lean_unbox_uint64(v_a_6346_);
lean_dec_ref(v_a_6346_);
v_res_6350_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_6341_, v_c_6342_, v___x_6343_, v___x_6344_, v___x_6345_, v_a_118275__boxed_6349_, v_a_6347_, v_a_6348_);
lean_dec_ref(v_c_6342_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_6351_, lean_object* v_x_6352_, lean_object* v_x_6353_, lean_object* v_x_6354_){
_start:
{
lean_object* v_ks_6355_; lean_object* v_vs_6356_; lean_object* v___x_6358_; uint8_t v_isShared_6359_; uint8_t v_isSharedCheck_6380_; 
v_ks_6355_ = lean_ctor_get(v_x_6351_, 0);
v_vs_6356_ = lean_ctor_get(v_x_6351_, 1);
v_isSharedCheck_6380_ = !lean_is_exclusive(v_x_6351_);
if (v_isSharedCheck_6380_ == 0)
{
v___x_6358_ = v_x_6351_;
v_isShared_6359_ = v_isSharedCheck_6380_;
goto v_resetjp_6357_;
}
else
{
lean_inc(v_vs_6356_);
lean_inc(v_ks_6355_);
lean_dec(v_x_6351_);
v___x_6358_ = lean_box(0);
v_isShared_6359_ = v_isSharedCheck_6380_;
goto v_resetjp_6357_;
}
v_resetjp_6357_:
{
lean_object* v___x_6360_; uint8_t v___x_6361_; 
v___x_6360_ = lean_array_get_size(v_ks_6355_);
v___x_6361_ = lean_nat_dec_lt(v_x_6352_, v___x_6360_);
if (v___x_6361_ == 0)
{
lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6365_; 
lean_dec(v_x_6352_);
v___x_6362_ = lean_array_push(v_ks_6355_, v_x_6353_);
v___x_6363_ = lean_array_push(v_vs_6356_, v_x_6354_);
if (v_isShared_6359_ == 0)
{
lean_ctor_set(v___x_6358_, 1, v___x_6363_);
lean_ctor_set(v___x_6358_, 0, v___x_6362_);
v___x_6365_ = v___x_6358_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6362_);
lean_ctor_set(v_reuseFailAlloc_6366_, 1, v___x_6363_);
v___x_6365_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
return v___x_6365_;
}
}
else
{
lean_object* v_k_x27_6367_; uint8_t v___x_6368_; 
v_k_x27_6367_ = lean_array_fget_borrowed(v_ks_6355_, v_x_6352_);
v___x_6368_ = l_Lean_instBEqMVarId_beq(v_x_6353_, v_k_x27_6367_);
if (v___x_6368_ == 0)
{
lean_object* v___x_6370_; 
if (v_isShared_6359_ == 0)
{
v___x_6370_ = v___x_6358_;
goto v_reusejp_6369_;
}
else
{
lean_object* v_reuseFailAlloc_6374_; 
v_reuseFailAlloc_6374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_ks_6355_);
lean_ctor_set(v_reuseFailAlloc_6374_, 1, v_vs_6356_);
v___x_6370_ = v_reuseFailAlloc_6374_;
goto v_reusejp_6369_;
}
v_reusejp_6369_:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; 
v___x_6371_ = lean_unsigned_to_nat(1u);
v___x_6372_ = lean_nat_add(v_x_6352_, v___x_6371_);
lean_dec(v_x_6352_);
v_x_6351_ = v___x_6370_;
v_x_6352_ = v___x_6372_;
goto _start;
}
}
else
{
lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6378_; 
v___x_6375_ = lean_array_fset(v_ks_6355_, v_x_6352_, v_x_6353_);
v___x_6376_ = lean_array_fset(v_vs_6356_, v_x_6352_, v_x_6354_);
lean_dec(v_x_6352_);
if (v_isShared_6359_ == 0)
{
lean_ctor_set(v___x_6358_, 1, v___x_6376_);
lean_ctor_set(v___x_6358_, 0, v___x_6375_);
v___x_6378_ = v___x_6358_;
goto v_reusejp_6377_;
}
else
{
lean_object* v_reuseFailAlloc_6379_; 
v_reuseFailAlloc_6379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6379_, 0, v___x_6375_);
lean_ctor_set(v_reuseFailAlloc_6379_, 1, v___x_6376_);
v___x_6378_ = v_reuseFailAlloc_6379_;
goto v_reusejp_6377_;
}
v_reusejp_6377_:
{
return v___x_6378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(lean_object* v_n_6381_, lean_object* v_k_6382_, lean_object* v_v_6383_){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; 
v___x_6384_ = lean_unsigned_to_nat(0u);
v___x_6385_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_n_6381_, v___x_6384_, v_k_6382_, v_v_6383_);
return v___x_6385_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_6386_; 
v___x_6386_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_6386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(lean_object* v_x_6387_, size_t v_x_6388_, size_t v_x_6389_, lean_object* v_x_6390_, lean_object* v_x_6391_){
_start:
{
if (lean_obj_tag(v_x_6387_) == 0)
{
lean_object* v_es_6392_; size_t v___x_6393_; size_t v___x_6394_; lean_object* v_j_6395_; lean_object* v___x_6396_; uint8_t v___x_6397_; 
v_es_6392_ = lean_ctor_get(v_x_6387_, 0);
v___x_6393_ = ((size_t)31ULL);
v___x_6394_ = lean_usize_land(v_x_6388_, v___x_6393_);
v_j_6395_ = lean_usize_to_nat(v___x_6394_);
v___x_6396_ = lean_array_get_size(v_es_6392_);
v___x_6397_ = lean_nat_dec_lt(v_j_6395_, v___x_6396_);
if (v___x_6397_ == 0)
{
lean_dec(v_j_6395_);
lean_dec(v_x_6391_);
lean_dec(v_x_6390_);
return v_x_6387_;
}
else
{
lean_object* v___x_6399_; uint8_t v_isShared_6400_; uint8_t v_isSharedCheck_6436_; 
lean_inc_ref(v_es_6392_);
v_isSharedCheck_6436_ = !lean_is_exclusive(v_x_6387_);
if (v_isSharedCheck_6436_ == 0)
{
lean_object* v_unused_6437_; 
v_unused_6437_ = lean_ctor_get(v_x_6387_, 0);
lean_dec(v_unused_6437_);
v___x_6399_ = v_x_6387_;
v_isShared_6400_ = v_isSharedCheck_6436_;
goto v_resetjp_6398_;
}
else
{
lean_dec(v_x_6387_);
v___x_6399_ = lean_box(0);
v_isShared_6400_ = v_isSharedCheck_6436_;
goto v_resetjp_6398_;
}
v_resetjp_6398_:
{
lean_object* v_v_6401_; lean_object* v___x_6402_; lean_object* v_xs_x27_6403_; lean_object* v___y_6405_; 
v_v_6401_ = lean_array_fget(v_es_6392_, v_j_6395_);
v___x_6402_ = lean_box(0);
v_xs_x27_6403_ = lean_array_fset(v_es_6392_, v_j_6395_, v___x_6402_);
switch(lean_obj_tag(v_v_6401_))
{
case 0:
{
lean_object* v_key_6410_; lean_object* v_val_6411_; lean_object* v___x_6413_; uint8_t v_isShared_6414_; uint8_t v_isSharedCheck_6421_; 
v_key_6410_ = lean_ctor_get(v_v_6401_, 0);
v_val_6411_ = lean_ctor_get(v_v_6401_, 1);
v_isSharedCheck_6421_ = !lean_is_exclusive(v_v_6401_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6413_ = v_v_6401_;
v_isShared_6414_ = v_isSharedCheck_6421_;
goto v_resetjp_6412_;
}
else
{
lean_inc(v_val_6411_);
lean_inc(v_key_6410_);
lean_dec(v_v_6401_);
v___x_6413_ = lean_box(0);
v_isShared_6414_ = v_isSharedCheck_6421_;
goto v_resetjp_6412_;
}
v_resetjp_6412_:
{
uint8_t v___x_6415_; 
v___x_6415_ = l_Lean_instBEqMVarId_beq(v_x_6390_, v_key_6410_);
if (v___x_6415_ == 0)
{
lean_object* v___x_6416_; lean_object* v___x_6417_; 
lean_del_object(v___x_6413_);
v___x_6416_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_6410_, v_val_6411_, v_x_6390_, v_x_6391_);
v___x_6417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6417_, 0, v___x_6416_);
v___y_6405_ = v___x_6417_;
goto v___jp_6404_;
}
else
{
lean_object* v___x_6419_; 
lean_dec(v_val_6411_);
lean_dec(v_key_6410_);
if (v_isShared_6414_ == 0)
{
lean_ctor_set(v___x_6413_, 1, v_x_6391_);
lean_ctor_set(v___x_6413_, 0, v_x_6390_);
v___x_6419_ = v___x_6413_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_x_6390_);
lean_ctor_set(v_reuseFailAlloc_6420_, 1, v_x_6391_);
v___x_6419_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
v___y_6405_ = v___x_6419_;
goto v___jp_6404_;
}
}
}
}
case 1:
{
lean_object* v_node_6422_; lean_object* v___x_6424_; uint8_t v_isShared_6425_; uint8_t v_isSharedCheck_6434_; 
v_node_6422_ = lean_ctor_get(v_v_6401_, 0);
v_isSharedCheck_6434_ = !lean_is_exclusive(v_v_6401_);
if (v_isSharedCheck_6434_ == 0)
{
v___x_6424_ = v_v_6401_;
v_isShared_6425_ = v_isSharedCheck_6434_;
goto v_resetjp_6423_;
}
else
{
lean_inc(v_node_6422_);
lean_dec(v_v_6401_);
v___x_6424_ = lean_box(0);
v_isShared_6425_ = v_isSharedCheck_6434_;
goto v_resetjp_6423_;
}
v_resetjp_6423_:
{
size_t v___x_6426_; size_t v___x_6427_; size_t v___x_6428_; size_t v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6432_; 
v___x_6426_ = ((size_t)5ULL);
v___x_6427_ = lean_usize_shift_right(v_x_6388_, v___x_6426_);
v___x_6428_ = ((size_t)1ULL);
v___x_6429_ = lean_usize_add(v_x_6389_, v___x_6428_);
v___x_6430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_node_6422_, v___x_6427_, v___x_6429_, v_x_6390_, v_x_6391_);
if (v_isShared_6425_ == 0)
{
lean_ctor_set(v___x_6424_, 0, v___x_6430_);
v___x_6432_ = v___x_6424_;
goto v_reusejp_6431_;
}
else
{
lean_object* v_reuseFailAlloc_6433_; 
v_reuseFailAlloc_6433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6433_, 0, v___x_6430_);
v___x_6432_ = v_reuseFailAlloc_6433_;
goto v_reusejp_6431_;
}
v_reusejp_6431_:
{
v___y_6405_ = v___x_6432_;
goto v___jp_6404_;
}
}
}
default: 
{
lean_object* v___x_6435_; 
v___x_6435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6435_, 0, v_x_6390_);
lean_ctor_set(v___x_6435_, 1, v_x_6391_);
v___y_6405_ = v___x_6435_;
goto v___jp_6404_;
}
}
v___jp_6404_:
{
lean_object* v___x_6406_; lean_object* v___x_6408_; 
v___x_6406_ = lean_array_fset(v_xs_x27_6403_, v_j_6395_, v___y_6405_);
lean_dec(v_j_6395_);
if (v_isShared_6400_ == 0)
{
lean_ctor_set(v___x_6399_, 0, v___x_6406_);
v___x_6408_ = v___x_6399_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v___x_6406_);
v___x_6408_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
return v___x_6408_;
}
}
}
}
}
else
{
lean_object* v_ks_6438_; lean_object* v_vs_6439_; lean_object* v___x_6441_; uint8_t v_isShared_6442_; uint8_t v_isSharedCheck_6457_; 
v_ks_6438_ = lean_ctor_get(v_x_6387_, 0);
v_vs_6439_ = lean_ctor_get(v_x_6387_, 1);
v_isSharedCheck_6457_ = !lean_is_exclusive(v_x_6387_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6441_ = v_x_6387_;
v_isShared_6442_ = v_isSharedCheck_6457_;
goto v_resetjp_6440_;
}
else
{
lean_inc(v_vs_6439_);
lean_inc(v_ks_6438_);
lean_dec(v_x_6387_);
v___x_6441_ = lean_box(0);
v_isShared_6442_ = v_isSharedCheck_6457_;
goto v_resetjp_6440_;
}
v_resetjp_6440_:
{
lean_object* v___x_6444_; 
if (v_isShared_6442_ == 0)
{
v___x_6444_ = v___x_6441_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_ks_6438_);
lean_ctor_set(v_reuseFailAlloc_6456_, 1, v_vs_6439_);
v___x_6444_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
lean_object* v_newNode_6445_; size_t v___x_6446_; uint8_t v___x_6447_; 
v_newNode_6445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v___x_6444_, v_x_6390_, v_x_6391_);
v___x_6446_ = ((size_t)7ULL);
v___x_6447_ = lean_usize_dec_le(v___x_6446_, v_x_6389_);
if (v___x_6447_ == 0)
{
lean_object* v___x_6448_; lean_object* v___x_6449_; uint8_t v___x_6450_; 
v___x_6448_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_6445_);
v___x_6449_ = lean_unsigned_to_nat(4u);
v___x_6450_ = lean_nat_dec_lt(v___x_6448_, v___x_6449_);
lean_dec(v___x_6448_);
if (v___x_6450_ == 0)
{
lean_object* v_ks_6451_; lean_object* v_vs_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; 
v_ks_6451_ = lean_ctor_get(v_newNode_6445_, 0);
lean_inc_ref(v_ks_6451_);
v_vs_6452_ = lean_ctor_get(v_newNode_6445_, 1);
lean_inc_ref(v_vs_6452_);
lean_dec_ref(v_newNode_6445_);
v___x_6453_ = lean_unsigned_to_nat(0u);
v___x_6454_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___closed__0);
v___x_6455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_x_6389_, v_ks_6451_, v_vs_6452_, v___x_6453_, v___x_6454_);
lean_dec_ref(v_vs_6452_);
lean_dec_ref(v_ks_6451_);
return v___x_6455_;
}
else
{
return v_newNode_6445_;
}
}
else
{
return v_newNode_6445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(size_t v_depth_6458_, lean_object* v_keys_6459_, lean_object* v_vals_6460_, lean_object* v_i_6461_, lean_object* v_entries_6462_){
_start:
{
lean_object* v___x_6463_; uint8_t v___x_6464_; 
v___x_6463_ = lean_array_get_size(v_keys_6459_);
v___x_6464_ = lean_nat_dec_lt(v_i_6461_, v___x_6463_);
if (v___x_6464_ == 0)
{
lean_dec(v_i_6461_);
return v_entries_6462_;
}
else
{
lean_object* v_k_6465_; lean_object* v_v_6466_; uint64_t v___x_6467_; size_t v_h_6468_; size_t v___x_6469_; lean_object* v___x_6470_; size_t v___x_6471_; size_t v___x_6472_; size_t v___x_6473_; size_t v_h_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; 
v_k_6465_ = lean_array_fget_borrowed(v_keys_6459_, v_i_6461_);
v_v_6466_ = lean_array_fget_borrowed(v_vals_6460_, v_i_6461_);
v___x_6467_ = l_Lean_instHashableMVarId_hash(v_k_6465_);
v_h_6468_ = lean_uint64_to_usize(v___x_6467_);
v___x_6469_ = ((size_t)5ULL);
v___x_6470_ = lean_unsigned_to_nat(1u);
v___x_6471_ = ((size_t)1ULL);
v___x_6472_ = lean_usize_sub(v_depth_6458_, v___x_6471_);
v___x_6473_ = lean_usize_mul(v___x_6469_, v___x_6472_);
v_h_6474_ = lean_usize_shift_right(v_h_6468_, v___x_6473_);
v___x_6475_ = lean_nat_add(v_i_6461_, v___x_6470_);
lean_dec(v_i_6461_);
lean_inc(v_v_6466_);
lean_inc(v_k_6465_);
v___x_6476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_entries_6462_, v_h_6474_, v_depth_6458_, v_k_6465_, v_v_6466_);
v_i_6461_ = v___x_6475_;
v_entries_6462_ = v___x_6476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_depth_6478_, lean_object* v_keys_6479_, lean_object* v_vals_6480_, lean_object* v_i_6481_, lean_object* v_entries_6482_){
_start:
{
size_t v_depth_boxed_6483_; lean_object* v_res_6484_; 
v_depth_boxed_6483_ = lean_unbox_usize(v_depth_6478_);
lean_dec(v_depth_6478_);
v_res_6484_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_boxed_6483_, v_keys_6479_, v_vals_6480_, v_i_6481_, v_entries_6482_);
lean_dec_ref(v_vals_6480_);
lean_dec_ref(v_keys_6479_);
return v_res_6484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_x_6485_, lean_object* v_x_6486_, lean_object* v_x_6487_, lean_object* v_x_6488_, lean_object* v_x_6489_){
_start:
{
size_t v_x_118423__boxed_6490_; size_t v_x_118424__boxed_6491_; lean_object* v_res_6492_; 
v_x_118423__boxed_6490_ = lean_unbox_usize(v_x_6486_);
lean_dec(v_x_6486_);
v_x_118424__boxed_6491_ = lean_unbox_usize(v_x_6487_);
lean_dec(v_x_6487_);
v_res_6492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6485_, v_x_118423__boxed_6490_, v_x_118424__boxed_6491_, v_x_6488_, v_x_6489_);
return v_res_6492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(lean_object* v_x_6493_, lean_object* v_x_6494_, lean_object* v_x_6495_){
_start:
{
uint64_t v___x_6496_; size_t v___x_6497_; size_t v___x_6498_; lean_object* v___x_6499_; 
v___x_6496_ = l_Lean_instHashableMVarId_hash(v_x_6494_);
v___x_6497_ = lean_uint64_to_usize(v___x_6496_);
v___x_6498_ = ((size_t)1ULL);
v___x_6499_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6493_, v___x_6497_, v___x_6498_, v_x_6494_, v_x_6495_);
return v___x_6499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_mvarId_6500_, lean_object* v_val_6501_, lean_object* v___y_6502_){
_start:
{
lean_object* v___x_6504_; lean_object* v_mctx_6505_; lean_object* v_cache_6506_; lean_object* v_zetaDeltaFVarIds_6507_; lean_object* v_postponed_6508_; lean_object* v_diag_6509_; lean_object* v___x_6511_; uint8_t v_isShared_6512_; uint8_t v_isSharedCheck_6538_; 
v___x_6504_ = lean_st_ref_take(v___y_6502_);
v_mctx_6505_ = lean_ctor_get(v___x_6504_, 0);
v_cache_6506_ = lean_ctor_get(v___x_6504_, 1);
v_zetaDeltaFVarIds_6507_ = lean_ctor_get(v___x_6504_, 2);
v_postponed_6508_ = lean_ctor_get(v___x_6504_, 3);
v_diag_6509_ = lean_ctor_get(v___x_6504_, 4);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6504_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6511_ = v___x_6504_;
v_isShared_6512_ = v_isSharedCheck_6538_;
goto v_resetjp_6510_;
}
else
{
lean_inc(v_diag_6509_);
lean_inc(v_postponed_6508_);
lean_inc(v_zetaDeltaFVarIds_6507_);
lean_inc(v_cache_6506_);
lean_inc(v_mctx_6505_);
lean_dec(v___x_6504_);
v___x_6511_ = lean_box(0);
v_isShared_6512_ = v_isSharedCheck_6538_;
goto v_resetjp_6510_;
}
v_resetjp_6510_:
{
lean_object* v_depth_6513_; lean_object* v_levelAssignDepth_6514_; lean_object* v_lmvarCounter_6515_; lean_object* v_mvarCounter_6516_; lean_object* v_lDecls_6517_; lean_object* v_decls_6518_; lean_object* v_userNames_6519_; lean_object* v_lAssignment_6520_; lean_object* v_eAssignment_6521_; lean_object* v_dAssignment_6522_; lean_object* v_instanceTypedMVars_6523_; lean_object* v___x_6525_; uint8_t v_isShared_6526_; uint8_t v_isSharedCheck_6537_; 
v_depth_6513_ = lean_ctor_get(v_mctx_6505_, 0);
v_levelAssignDepth_6514_ = lean_ctor_get(v_mctx_6505_, 1);
v_lmvarCounter_6515_ = lean_ctor_get(v_mctx_6505_, 2);
v_mvarCounter_6516_ = lean_ctor_get(v_mctx_6505_, 3);
v_lDecls_6517_ = lean_ctor_get(v_mctx_6505_, 4);
v_decls_6518_ = lean_ctor_get(v_mctx_6505_, 5);
v_userNames_6519_ = lean_ctor_get(v_mctx_6505_, 6);
v_lAssignment_6520_ = lean_ctor_get(v_mctx_6505_, 7);
v_eAssignment_6521_ = lean_ctor_get(v_mctx_6505_, 8);
v_dAssignment_6522_ = lean_ctor_get(v_mctx_6505_, 9);
v_instanceTypedMVars_6523_ = lean_ctor_get(v_mctx_6505_, 10);
v_isSharedCheck_6537_ = !lean_is_exclusive(v_mctx_6505_);
if (v_isSharedCheck_6537_ == 0)
{
v___x_6525_ = v_mctx_6505_;
v_isShared_6526_ = v_isSharedCheck_6537_;
goto v_resetjp_6524_;
}
else
{
lean_inc(v_instanceTypedMVars_6523_);
lean_inc(v_dAssignment_6522_);
lean_inc(v_eAssignment_6521_);
lean_inc(v_lAssignment_6520_);
lean_inc(v_userNames_6519_);
lean_inc(v_decls_6518_);
lean_inc(v_lDecls_6517_);
lean_inc(v_mvarCounter_6516_);
lean_inc(v_lmvarCounter_6515_);
lean_inc(v_levelAssignDepth_6514_);
lean_inc(v_depth_6513_);
lean_dec(v_mctx_6505_);
v___x_6525_ = lean_box(0);
v_isShared_6526_ = v_isSharedCheck_6537_;
goto v_resetjp_6524_;
}
v_resetjp_6524_:
{
lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6530_; 
v___x_6527_ = lean_box(0);
v___x_6528_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_eAssignment_6521_, v_mvarId_6500_, v_val_6501_);
if (v_isShared_6526_ == 0)
{
lean_ctor_set(v___x_6525_, 8, v___x_6528_);
v___x_6530_ = v___x_6525_;
goto v_reusejp_6529_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_depth_6513_);
lean_ctor_set(v_reuseFailAlloc_6536_, 1, v_levelAssignDepth_6514_);
lean_ctor_set(v_reuseFailAlloc_6536_, 2, v_lmvarCounter_6515_);
lean_ctor_set(v_reuseFailAlloc_6536_, 3, v_mvarCounter_6516_);
lean_ctor_set(v_reuseFailAlloc_6536_, 4, v_lDecls_6517_);
lean_ctor_set(v_reuseFailAlloc_6536_, 5, v_decls_6518_);
lean_ctor_set(v_reuseFailAlloc_6536_, 6, v_userNames_6519_);
lean_ctor_set(v_reuseFailAlloc_6536_, 7, v_lAssignment_6520_);
lean_ctor_set(v_reuseFailAlloc_6536_, 8, v___x_6528_);
lean_ctor_set(v_reuseFailAlloc_6536_, 9, v_dAssignment_6522_);
lean_ctor_set(v_reuseFailAlloc_6536_, 10, v_instanceTypedMVars_6523_);
v___x_6530_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6529_;
}
v_reusejp_6529_:
{
lean_object* v___x_6532_; 
if (v_isShared_6512_ == 0)
{
lean_ctor_set(v___x_6511_, 0, v___x_6530_);
v___x_6532_ = v___x_6511_;
goto v_reusejp_6531_;
}
else
{
lean_object* v_reuseFailAlloc_6535_; 
v_reuseFailAlloc_6535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6535_, 0, v___x_6530_);
lean_ctor_set(v_reuseFailAlloc_6535_, 1, v_cache_6506_);
lean_ctor_set(v_reuseFailAlloc_6535_, 2, v_zetaDeltaFVarIds_6507_);
lean_ctor_set(v_reuseFailAlloc_6535_, 3, v_postponed_6508_);
lean_ctor_set(v_reuseFailAlloc_6535_, 4, v_diag_6509_);
v___x_6532_ = v_reuseFailAlloc_6535_;
goto v_reusejp_6531_;
}
v_reusejp_6531_:
{
lean_object* v___x_6533_; lean_object* v___x_6534_; 
v___x_6533_ = lean_st_ref_put(v___y_6502_, v___x_6532_);
v___x_6534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6534_, 0, v___x_6527_);
return v___x_6534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_mvarId_6539_, lean_object* v_val_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_){
_start:
{
lean_object* v_res_6543_; 
v_res_6543_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6539_, v_val_6540_, v___y_6541_);
lean_dec(v___y_6541_);
return v_res_6543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(lean_object* v_goal_6548_, lean_object* v_c_6549_, lean_object* v_numCases_6550_, uint8_t v_isRec_6551_, lean_object* v_candidates_x3f_6552_, uint8_t v_compress_6553_, lean_object* v_kp_6554_, uint8_t v_stopAtFirstFailure_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_){
_start:
{
lean_object* v___x_6566_; 
v___x_6566_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_6557_);
if (lean_obj_tag(v___x_6566_) == 0)
{
lean_object* v_a_6567_; uint8_t v_trace_6568_; lean_object* v___x_6569_; 
v_a_6567_ = lean_ctor_get(v___x_6566_, 0);
lean_inc(v_a_6567_);
lean_dec_ref_known(v___x_6566_, 1);
v_trace_6568_ = lean_ctor_get_uint8(v_a_6567_, sizeof(void*)*18);
lean_dec(v_a_6567_);
v___x_6569_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v___y_6557_, v___y_6558_, v___y_6562_, v___y_6564_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v_a_6570_; lean_object* v___x_6571_; 
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
lean_inc(v_a_6570_);
lean_dec_ref_known(v___x_6569_, 1);
lean_inc_ref(v_goal_6548_);
v___x_6571_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_6548_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
if (lean_obj_tag(v___x_6571_) == 0)
{
lean_object* v_a_6572_; lean_object* v_mvarId_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___f_6576_; lean_object* v___x_6577_; lean_object* v___f_6578_; lean_object* v___x_6579_; 
v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
lean_inc_n(v_a_6572_, 2);
lean_dec_ref_known(v___x_6571_, 1);
v_mvarId_6573_ = lean_ctor_get(v_goal_6548_, 1);
v___x_6574_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6549_);
v___x_6575_ = lean_box(v_isRec_6551_);
lean_inc_ref_n(v_c_6549_, 2);
lean_inc_ref(v___x_6574_);
v___f_6576_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6576_, 0, v___x_6574_);
lean_closure_set(v___f_6576_, 1, v_c_6549_);
lean_closure_set(v___f_6576_, 2, v_a_6572_);
lean_closure_set(v___f_6576_, 3, v_numCases_6550_);
lean_closure_set(v___f_6576_, 4, v___x_6575_);
v___x_6577_ = lean_box(v_trace_6568_);
lean_inc_ref(v_goal_6548_);
v___f_6578_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_6578_, 0, v_goal_6548_);
lean_closure_set(v___f_6578_, 1, v___x_6577_);
lean_closure_set(v___f_6578_, 2, v___f_6576_);
lean_closure_set(v___f_6578_, 3, v_c_6549_);
lean_closure_set(v___f_6578_, 4, v_candidates_x3f_6552_);
lean_inc(v_mvarId_6573_);
v___x_6579_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6573_, v___f_6578_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
if (lean_obj_tag(v___x_6579_) == 0)
{
lean_object* v_a_6580_; lean_object* v___x_6582_; uint8_t v_isShared_6583_; uint8_t v_isSharedCheck_6759_; 
v_a_6580_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6759_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6759_ == 0)
{
v___x_6582_ = v___x_6579_;
v_isShared_6583_ = v_isSharedCheck_6759_;
goto v_resetjp_6581_;
}
else
{
lean_inc(v_a_6580_);
lean_dec(v___x_6579_);
v___x_6582_ = lean_box(0);
v_isShared_6583_ = v_isSharedCheck_6759_;
goto v_resetjp_6581_;
}
v_resetjp_6581_:
{
lean_object* v_fst_6584_; lean_object* v_snd_6585_; lean_object* v___x_6587_; uint8_t v_isShared_6588_; uint8_t v_isSharedCheck_6758_; 
v_fst_6584_ = lean_ctor_get(v_a_6580_, 0);
v_snd_6585_ = lean_ctor_get(v_a_6580_, 1);
v_isSharedCheck_6758_ = !lean_is_exclusive(v_a_6580_);
if (v_isSharedCheck_6758_ == 0)
{
v___x_6587_ = v_a_6580_;
v_isShared_6588_ = v_isSharedCheck_6758_;
goto v_resetjp_6586_;
}
else
{
lean_inc(v_snd_6585_);
lean_inc(v_fst_6584_);
lean_dec(v_a_6580_);
v___x_6587_ = lean_box(0);
v_isShared_6588_ = v_isSharedCheck_6758_;
goto v_resetjp_6586_;
}
v_resetjp_6586_:
{
lean_object* v_fst_6589_; lean_object* v_snd_6590_; lean_object* v___x_6592_; uint8_t v_isShared_6593_; uint8_t v_isSharedCheck_6757_; 
v_fst_6589_ = lean_ctor_get(v_fst_6584_, 0);
v_snd_6590_ = lean_ctor_get(v_fst_6584_, 1);
v_isSharedCheck_6757_ = !lean_is_exclusive(v_fst_6584_);
if (v_isSharedCheck_6757_ == 0)
{
v___x_6592_ = v_fst_6584_;
v_isShared_6593_ = v_isSharedCheck_6757_;
goto v_resetjp_6591_;
}
else
{
lean_inc(v_snd_6590_);
lean_inc(v_fst_6589_);
lean_dec(v_fst_6584_);
v___x_6592_ = lean_box(0);
v_isShared_6593_ = v_isSharedCheck_6757_;
goto v_resetjp_6591_;
}
v_resetjp_6591_:
{
lean_object* v___y_6595_; lean_object* v___y_6596_; lean_object* v___y_6597_; lean_object* v___y_6598_; lean_object* v___y_6599_; lean_object* v___f_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v_congrThms_6649_; lean_object* v_simp_6650_; lean_object* v_symSimp_6651_; lean_object* v_symDSimp_6652_; lean_object* v_lastTag_6653_; lean_object* v_counters_6654_; lean_object* v_splitDiags_6655_; lean_object* v_ematchDiags_6656_; lean_object* v_lawfulEqCmpMap_6657_; lean_object* v_reflCmpMap_6658_; lean_object* v_anchors_6659_; lean_object* v_fvarAnchors_6660_; lean_object* v_instanceMap_6661_; lean_object* v_hoistedDecls_6662_; lean_object* v_proofInfos_6663_; lean_object* v_numBranches_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6756_; 
lean_inc(v_snd_6585_);
v___f_6646_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed), 12, 2);
lean_closure_set(v___f_6646_, 0, v_snd_6585_);
lean_closure_set(v___f_6646_, 1, v_a_6572_);
v___x_6647_ = l_List_lengthTR___redArg(v_fst_6589_);
v___x_6648_ = lean_st_ref_take(v___y_6558_);
v_congrThms_6649_ = lean_ctor_get(v___x_6648_, 0);
v_simp_6650_ = lean_ctor_get(v___x_6648_, 1);
v_symSimp_6651_ = lean_ctor_get(v___x_6648_, 2);
v_symDSimp_6652_ = lean_ctor_get(v___x_6648_, 3);
v_lastTag_6653_ = lean_ctor_get(v___x_6648_, 4);
v_counters_6654_ = lean_ctor_get(v___x_6648_, 5);
v_splitDiags_6655_ = lean_ctor_get(v___x_6648_, 6);
v_ematchDiags_6656_ = lean_ctor_get(v___x_6648_, 7);
v_lawfulEqCmpMap_6657_ = lean_ctor_get(v___x_6648_, 8);
v_reflCmpMap_6658_ = lean_ctor_get(v___x_6648_, 9);
v_anchors_6659_ = lean_ctor_get(v___x_6648_, 10);
v_fvarAnchors_6660_ = lean_ctor_get(v___x_6648_, 11);
v_instanceMap_6661_ = lean_ctor_get(v___x_6648_, 12);
v_hoistedDecls_6662_ = lean_ctor_get(v___x_6648_, 13);
v_proofInfos_6663_ = lean_ctor_get(v___x_6648_, 14);
v_numBranches_6664_ = lean_ctor_get(v___x_6648_, 15);
v_isSharedCheck_6756_ = !lean_is_exclusive(v___x_6648_);
if (v_isSharedCheck_6756_ == 0)
{
v___x_6666_ = v___x_6648_;
v_isShared_6667_ = v_isSharedCheck_6756_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_numBranches_6664_);
lean_inc(v_proofInfos_6663_);
lean_inc(v_hoistedDecls_6662_);
lean_inc(v_instanceMap_6661_);
lean_inc(v_fvarAnchors_6660_);
lean_inc(v_anchors_6659_);
lean_inc(v_reflCmpMap_6658_);
lean_inc(v_lawfulEqCmpMap_6657_);
lean_inc(v_ematchDiags_6656_);
lean_inc(v_splitDiags_6655_);
lean_inc(v_counters_6654_);
lean_inc(v_lastTag_6653_);
lean_inc(v_symDSimp_6652_);
lean_inc(v_symSimp_6651_);
lean_inc(v_simp_6650_);
lean_inc(v_congrThms_6649_);
lean_dec(v___x_6648_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6756_;
goto v_resetjp_6665_;
}
v___jp_6594_:
{
lean_object* v___x_6600_; uint8_t v___x_6601_; 
v___x_6600_ = lean_array_get_size(v___y_6597_);
v___x_6601_ = lean_nat_dec_eq(v___x_6600_, v___y_6595_);
if (v___x_6601_ == 0)
{
lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6605_; 
lean_dec(v___y_6596_);
lean_dec(v_snd_6590_);
v___x_6602_ = lean_array_to_list(v___y_6597_);
v___x_6603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6603_, 0, v___x_6602_);
if (v_isShared_6583_ == 0)
{
lean_ctor_set(v___x_6582_, 0, v___x_6603_);
v___x_6605_ = v___x_6582_;
goto v_reusejp_6604_;
}
else
{
lean_object* v_reuseFailAlloc_6606_; 
v_reuseFailAlloc_6606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6606_, 0, v___x_6603_);
v___x_6605_ = v_reuseFailAlloc_6606_;
goto v_reusejp_6604_;
}
v_reusejp_6604_:
{
return v___x_6605_;
}
}
else
{
lean_dec(v___y_6597_);
if (lean_obj_tag(v_snd_6590_) == 1)
{
lean_object* v_val_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6641_; 
lean_del_object(v___x_6582_);
v_val_6607_ = lean_ctor_get(v_snd_6590_, 0);
v_isSharedCheck_6641_ = !lean_is_exclusive(v_snd_6590_);
if (v_isSharedCheck_6641_ == 0)
{
v___x_6609_ = v_snd_6590_;
v_isShared_6610_ = v_isSharedCheck_6641_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_val_6607_);
lean_dec(v_snd_6590_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6641_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v___x_6611_; 
v___x_6611_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_6607_, v___y_6598_);
lean_dec(v_val_6607_);
if (lean_obj_tag(v___x_6611_) == 0)
{
lean_object* v_a_6612_; lean_object* v___x_6613_; 
v_a_6612_ = lean_ctor_get(v___x_6611_, 0);
lean_inc(v_a_6612_);
lean_dec_ref_known(v___x_6611_, 1);
v___x_6613_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_6612_, v___y_6596_, v_compress_6553_, v___y_6598_, v___y_6599_);
if (lean_obj_tag(v___x_6613_) == 0)
{
lean_object* v_a_6614_; lean_object* v___x_6616_; uint8_t v_isShared_6617_; uint8_t v_isSharedCheck_6624_; 
v_a_6614_ = lean_ctor_get(v___x_6613_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6613_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6616_ = v___x_6613_;
v_isShared_6617_ = v_isSharedCheck_6624_;
goto v_resetjp_6615_;
}
else
{
lean_inc(v_a_6614_);
lean_dec(v___x_6613_);
v___x_6616_ = lean_box(0);
v_isShared_6617_ = v_isSharedCheck_6624_;
goto v_resetjp_6615_;
}
v_resetjp_6615_:
{
lean_object* v___x_6619_; 
if (v_isShared_6610_ == 0)
{
lean_ctor_set_tag(v___x_6609_, 0);
lean_ctor_set(v___x_6609_, 0, v_a_6614_);
v___x_6619_ = v___x_6609_;
goto v_reusejp_6618_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_a_6614_);
v___x_6619_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6618_;
}
v_reusejp_6618_:
{
lean_object* v___x_6621_; 
if (v_isShared_6617_ == 0)
{
lean_ctor_set(v___x_6616_, 0, v___x_6619_);
v___x_6621_ = v___x_6616_;
goto v_reusejp_6620_;
}
else
{
lean_object* v_reuseFailAlloc_6622_; 
v_reuseFailAlloc_6622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6622_, 0, v___x_6619_);
v___x_6621_ = v_reuseFailAlloc_6622_;
goto v_reusejp_6620_;
}
v_reusejp_6620_:
{
return v___x_6621_;
}
}
}
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_del_object(v___x_6609_);
v_a_6625_ = lean_ctor_get(v___x_6613_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6613_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6613_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6613_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v___x_6630_; 
if (v_isShared_6628_ == 0)
{
v___x_6630_ = v___x_6627_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6631_; 
v_reuseFailAlloc_6631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6631_, 0, v_a_6625_);
v___x_6630_ = v_reuseFailAlloc_6631_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
return v___x_6630_;
}
}
}
}
else
{
lean_object* v_a_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6640_; 
lean_del_object(v___x_6609_);
lean_dec(v___y_6596_);
v_a_6633_ = lean_ctor_get(v___x_6611_, 0);
v_isSharedCheck_6640_ = !lean_is_exclusive(v___x_6611_);
if (v_isSharedCheck_6640_ == 0)
{
v___x_6635_ = v___x_6611_;
v_isShared_6636_ = v_isSharedCheck_6640_;
goto v_resetjp_6634_;
}
else
{
lean_inc(v_a_6633_);
lean_dec(v___x_6611_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6640_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
lean_object* v___x_6638_; 
if (v_isShared_6636_ == 0)
{
v___x_6638_ = v___x_6635_;
goto v_reusejp_6637_;
}
else
{
lean_object* v_reuseFailAlloc_6639_; 
v_reuseFailAlloc_6639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6639_, 0, v_a_6633_);
v___x_6638_ = v_reuseFailAlloc_6639_;
goto v_reusejp_6637_;
}
v_reusejp_6637_:
{
return v___x_6638_;
}
}
}
}
}
else
{
lean_object* v___x_6642_; lean_object* v___x_6644_; 
lean_dec(v___y_6596_);
lean_dec(v_snd_6590_);
v___x_6642_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__0));
if (v_isShared_6583_ == 0)
{
lean_ctor_set(v___x_6582_, 0, v___x_6642_);
v___x_6644_ = v___x_6582_;
goto v_reusejp_6643_;
}
else
{
lean_object* v_reuseFailAlloc_6645_; 
v_reuseFailAlloc_6645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6645_, 0, v___x_6642_);
v___x_6644_ = v_reuseFailAlloc_6645_;
goto v_reusejp_6643_;
}
v_reusejp_6643_:
{
return v___x_6644_;
}
}
}
}
v_resetjp_6665_:
{
lean_object* v___y_6669_; 
if (v_isRec_6551_ == 0)
{
lean_object* v___x_6754_; lean_object* v___x_6755_; 
v___x_6754_ = lean_unsigned_to_nat(1u);
v___x_6755_ = lean_nat_sub(v___x_6647_, v___x_6754_);
v___y_6669_ = v___x_6755_;
goto v___jp_6668_;
}
else
{
lean_inc(v___x_6647_);
v___y_6669_ = v___x_6647_;
goto v___jp_6668_;
}
v___jp_6668_:
{
lean_object* v___x_6670_; lean_object* v___x_6672_; 
v___x_6670_ = lean_nat_add(v_numBranches_6664_, v___y_6669_);
lean_dec(v___y_6669_);
lean_dec(v_numBranches_6664_);
if (v_isShared_6667_ == 0)
{
lean_ctor_set(v___x_6666_, 15, v___x_6670_);
v___x_6672_ = v___x_6666_;
goto v_reusejp_6671_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_congrThms_6649_);
lean_ctor_set(v_reuseFailAlloc_6753_, 1, v_simp_6650_);
lean_ctor_set(v_reuseFailAlloc_6753_, 2, v_symSimp_6651_);
lean_ctor_set(v_reuseFailAlloc_6753_, 3, v_symDSimp_6652_);
lean_ctor_set(v_reuseFailAlloc_6753_, 4, v_lastTag_6653_);
lean_ctor_set(v_reuseFailAlloc_6753_, 5, v_counters_6654_);
lean_ctor_set(v_reuseFailAlloc_6753_, 6, v_splitDiags_6655_);
lean_ctor_set(v_reuseFailAlloc_6753_, 7, v_ematchDiags_6656_);
lean_ctor_set(v_reuseFailAlloc_6753_, 8, v_lawfulEqCmpMap_6657_);
lean_ctor_set(v_reuseFailAlloc_6753_, 9, v_reflCmpMap_6658_);
lean_ctor_set(v_reuseFailAlloc_6753_, 10, v_anchors_6659_);
lean_ctor_set(v_reuseFailAlloc_6753_, 11, v_fvarAnchors_6660_);
lean_ctor_set(v_reuseFailAlloc_6753_, 12, v_instanceMap_6661_);
lean_ctor_set(v_reuseFailAlloc_6753_, 13, v_hoistedDecls_6662_);
lean_ctor_set(v_reuseFailAlloc_6753_, 14, v_proofInfos_6663_);
lean_ctor_set(v_reuseFailAlloc_6753_, 15, v___x_6670_);
v___x_6672_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6671_;
}
v_reusejp_6671_:
{
lean_object* v___x_6673_; lean_object* v_toGoalState_6674_; lean_object* v_mvarId_6675_; lean_object* v_goalStack_6676_; lean_object* v___x_6678_; 
v___x_6673_ = lean_st_ref_put(v___y_6558_, v___x_6672_);
v_toGoalState_6674_ = lean_ctor_get(v_snd_6585_, 0);
v_mvarId_6675_ = lean_ctor_get(v_snd_6585_, 1);
lean_inc_n(v_mvarId_6675_, 2);
v_goalStack_6676_ = lean_ctor_get(v_toGoalState_6674_, 18);
lean_inc_ref(v_goalStack_6676_);
lean_inc_ref(v_toGoalState_6674_);
if (v_isShared_6593_ == 0)
{
lean_ctor_set(v___x_6592_, 1, v_toGoalState_6674_);
lean_ctor_set(v___x_6592_, 0, v_mvarId_6675_);
v___x_6678_ = v___x_6592_;
goto v_reusejp_6677_;
}
else
{
lean_object* v_reuseFailAlloc_6752_; 
v_reuseFailAlloc_6752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6752_, 0, v_mvarId_6675_);
lean_ctor_set(v_reuseFailAlloc_6752_, 1, v_toGoalState_6674_);
v___x_6678_ = v_reuseFailAlloc_6752_;
goto v_reusejp_6677_;
}
v_reusejp_6677_:
{
lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; 
lean_inc_ref(v_goalStack_6676_);
v___x_6679_ = lean_array_push(v_goalStack_6676_, v___x_6678_);
lean_inc_ref(v_c_6549_);
v___x_6680_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_6680_, 0, v_c_6549_);
lean_inc(v_mvarId_6675_);
v___x_6681_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6675_, v___x_6680_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
if (lean_obj_tag(v___x_6681_) == 0)
{
lean_object* v_a_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; uint64_t v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6691_; 
v_a_6682_ = lean_ctor_get(v___x_6681_, 0);
lean_inc(v_a_6682_);
lean_dec_ref_known(v___x_6681_, 1);
v___x_6683_ = lean_unsigned_to_nat(0u);
v___x_6684_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___closed__1));
v___x_6685_ = lean_unbox_uint64(v_a_6682_);
lean_dec(v_a_6682_);
lean_inc_n(v___x_6647_, 2);
lean_inc_ref(v_toGoalState_6674_);
v___x_6686_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_toGoalState_6674_, v_c_6549_, v___x_6574_, v___x_6647_, v___x_6679_, v___x_6685_, v_fst_6589_, v___x_6684_);
lean_dec_ref(v_c_6549_);
v___x_6687_ = lean_box(0);
v___x_6688_ = lean_unsigned_to_nat(1u);
v___x_6689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6689_, 0, v___x_6683_);
lean_ctor_set(v___x_6689_, 1, v___x_6647_);
lean_ctor_set(v___x_6689_, 2, v___x_6688_);
if (v_isShared_6588_ == 0)
{
lean_ctor_set(v___x_6587_, 1, v___x_6689_);
lean_ctor_set(v___x_6587_, 0, v___x_6687_);
v___x_6691_ = v___x_6587_;
goto v_reusejp_6690_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v___x_6687_);
lean_ctor_set(v_reuseFailAlloc_6743_, 1, v___x_6689_);
v___x_6691_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6690_;
}
v_reusejp_6690_:
{
lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; 
v___x_6692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6692_, 0, v___x_6684_);
lean_ctor_set(v___x_6692_, 1, v___x_6691_);
v___x_6693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6693_, 0, v___x_6684_);
lean_ctor_set(v___x_6693_, 1, v___x_6692_);
v___x_6694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6694_, 0, v___x_6687_);
lean_ctor_set(v___x_6694_, 1, v___x_6693_);
lean_inc(v_mvarId_6675_);
v___x_6695_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6554_, v_a_6570_, v_goal_6548_, v___x_6647_, v_snd_6585_, v_mvarId_6675_, v_stopAtFirstFailure_6555_, v_goalStack_6676_, v___x_6686_, v___x_6694_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
lean_dec(v___x_6686_);
lean_dec_ref(v_goalStack_6676_);
lean_dec(v___x_6647_);
if (lean_obj_tag(v___x_6695_) == 0)
{
lean_object* v_a_6696_; lean_object* v___x_6698_; uint8_t v_isShared_6699_; uint8_t v_isSharedCheck_6734_; 
v_a_6696_ = lean_ctor_get(v___x_6695_, 0);
v_isSharedCheck_6734_ = !lean_is_exclusive(v___x_6695_);
if (v_isSharedCheck_6734_ == 0)
{
v___x_6698_ = v___x_6695_;
v_isShared_6699_ = v_isSharedCheck_6734_;
goto v_resetjp_6697_;
}
else
{
lean_inc(v_a_6696_);
lean_dec(v___x_6695_);
v___x_6698_ = lean_box(0);
v_isShared_6699_ = v_isSharedCheck_6734_;
goto v_resetjp_6697_;
}
v_resetjp_6697_:
{
lean_object* v_fst_6700_; 
v_fst_6700_ = lean_ctor_get(v_a_6696_, 0);
if (lean_obj_tag(v_fst_6700_) == 0)
{
lean_object* v_snd_6701_; lean_object* v_snd_6702_; lean_object* v_fst_6703_; lean_object* v_fst_6704_; lean_object* v___x_6705_; 
lean_del_object(v___x_6698_);
v_snd_6701_ = lean_ctor_get(v_a_6696_, 1);
lean_inc(v_snd_6701_);
lean_dec(v_a_6696_);
v_snd_6702_ = lean_ctor_get(v_snd_6701_, 1);
lean_inc(v_snd_6702_);
v_fst_6703_ = lean_ctor_get(v_snd_6701_, 0);
lean_inc(v_fst_6703_);
lean_dec(v_snd_6701_);
v_fst_6704_ = lean_ctor_get(v_snd_6702_, 0);
lean_inc(v_fst_6704_);
lean_dec(v_snd_6702_);
lean_inc(v_mvarId_6675_);
v___x_6705_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_6675_, v___f_6646_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
if (lean_obj_tag(v___x_6705_) == 0)
{
lean_object* v_a_6706_; lean_object* v___x_6707_; 
v_a_6706_ = lean_ctor_get(v___x_6705_, 0);
lean_inc(v_a_6706_);
lean_dec_ref_known(v___x_6705_, 1);
lean_inc(v_mvarId_6675_);
v___x_6707_ = l_Lean_MVarId_getType(v_mvarId_6675_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
if (lean_obj_tag(v___x_6707_) == 0)
{
lean_object* v_a_6708_; uint8_t v___x_6709_; 
v_a_6708_ = lean_ctor_get(v___x_6707_, 0);
lean_inc(v_a_6708_);
lean_dec_ref_known(v___x_6707_, 1);
v___x_6709_ = l_Lean_Expr_isFalse(v_a_6708_);
lean_dec(v_a_6708_);
if (v___x_6709_ == 0)
{
lean_object* v___x_6710_; 
v___x_6710_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6675_, v_a_6706_, v___y_6562_);
lean_dec_ref(v___x_6710_);
v___y_6595_ = v___x_6683_;
v___y_6596_ = v_fst_6703_;
v___y_6597_ = v_fst_6704_;
v___y_6598_ = v___y_6563_;
v___y_6599_ = v___y_6564_;
goto v___jp_6594_;
}
else
{
lean_object* v___x_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; 
v___x_6711_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___lam__1___closed__1);
v___x_6712_ = l_Lean_Meta_mkExpectedPropHint(v_a_6706_, v___x_6711_);
v___x_6713_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6675_, v___x_6712_, v___y_6562_);
lean_dec_ref(v___x_6713_);
v___y_6595_ = v___x_6683_;
v___y_6596_ = v_fst_6703_;
v___y_6597_ = v_fst_6704_;
v___y_6598_ = v___y_6563_;
v___y_6599_ = v___y_6564_;
goto v___jp_6594_;
}
}
else
{
lean_object* v_a_6714_; lean_object* v___x_6716_; uint8_t v_isShared_6717_; uint8_t v_isSharedCheck_6721_; 
lean_dec(v_a_6706_);
lean_dec(v_fst_6704_);
lean_dec(v_fst_6703_);
lean_dec(v_mvarId_6675_);
lean_dec(v_snd_6590_);
lean_del_object(v___x_6582_);
v_a_6714_ = lean_ctor_get(v___x_6707_, 0);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6707_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6716_ = v___x_6707_;
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
else
{
lean_inc(v_a_6714_);
lean_dec(v___x_6707_);
v___x_6716_ = lean_box(0);
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
v_resetjp_6715_:
{
lean_object* v___x_6719_; 
if (v_isShared_6717_ == 0)
{
v___x_6719_ = v___x_6716_;
goto v_reusejp_6718_;
}
else
{
lean_object* v_reuseFailAlloc_6720_; 
v_reuseFailAlloc_6720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6720_, 0, v_a_6714_);
v___x_6719_ = v_reuseFailAlloc_6720_;
goto v_reusejp_6718_;
}
v_reusejp_6718_:
{
return v___x_6719_;
}
}
}
}
else
{
lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6729_; 
lean_dec(v_fst_6704_);
lean_dec(v_fst_6703_);
lean_dec(v_mvarId_6675_);
lean_dec(v_snd_6590_);
lean_del_object(v___x_6582_);
v_a_6722_ = lean_ctor_get(v___x_6705_, 0);
v_isSharedCheck_6729_ = !lean_is_exclusive(v___x_6705_);
if (v_isSharedCheck_6729_ == 0)
{
v___x_6724_ = v___x_6705_;
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_dec(v___x_6705_);
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
lean_object* v_val_6730_; lean_object* v___x_6732_; 
lean_inc_ref(v_fst_6700_);
lean_dec(v_a_6696_);
lean_dec(v_mvarId_6675_);
lean_dec_ref(v___f_6646_);
lean_dec(v_snd_6590_);
lean_del_object(v___x_6582_);
v_val_6730_ = lean_ctor_get(v_fst_6700_, 0);
lean_inc(v_val_6730_);
lean_dec_ref_known(v_fst_6700_, 1);
if (v_isShared_6699_ == 0)
{
lean_ctor_set(v___x_6698_, 0, v_val_6730_);
v___x_6732_ = v___x_6698_;
goto v_reusejp_6731_;
}
else
{
lean_object* v_reuseFailAlloc_6733_; 
v_reuseFailAlloc_6733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_val_6730_);
v___x_6732_ = v_reuseFailAlloc_6733_;
goto v_reusejp_6731_;
}
v_reusejp_6731_:
{
return v___x_6732_;
}
}
}
}
else
{
lean_object* v_a_6735_; lean_object* v___x_6737_; uint8_t v_isShared_6738_; uint8_t v_isSharedCheck_6742_; 
lean_dec(v_mvarId_6675_);
lean_dec_ref(v___f_6646_);
lean_dec(v_snd_6590_);
lean_del_object(v___x_6582_);
v_a_6735_ = lean_ctor_get(v___x_6695_, 0);
v_isSharedCheck_6742_ = !lean_is_exclusive(v___x_6695_);
if (v_isSharedCheck_6742_ == 0)
{
v___x_6737_ = v___x_6695_;
v_isShared_6738_ = v_isSharedCheck_6742_;
goto v_resetjp_6736_;
}
else
{
lean_inc(v_a_6735_);
lean_dec(v___x_6695_);
v___x_6737_ = lean_box(0);
v_isShared_6738_ = v_isSharedCheck_6742_;
goto v_resetjp_6736_;
}
v_resetjp_6736_:
{
lean_object* v___x_6740_; 
if (v_isShared_6738_ == 0)
{
v___x_6740_ = v___x_6737_;
goto v_reusejp_6739_;
}
else
{
lean_object* v_reuseFailAlloc_6741_; 
v_reuseFailAlloc_6741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6741_, 0, v_a_6735_);
v___x_6740_ = v_reuseFailAlloc_6741_;
goto v_reusejp_6739_;
}
v_reusejp_6739_:
{
return v___x_6740_;
}
}
}
}
}
else
{
lean_object* v_a_6744_; lean_object* v___x_6746_; uint8_t v_isShared_6747_; uint8_t v_isSharedCheck_6751_; 
lean_dec_ref(v___x_6679_);
lean_dec_ref(v_goalStack_6676_);
lean_dec(v_mvarId_6675_);
lean_dec(v___x_6647_);
lean_dec_ref(v___f_6646_);
lean_dec(v_snd_6590_);
lean_dec(v_fst_6589_);
lean_del_object(v___x_6587_);
lean_dec(v_snd_6585_);
lean_del_object(v___x_6582_);
lean_dec_ref(v___x_6574_);
lean_dec(v_a_6570_);
lean_dec_ref(v_kp_6554_);
lean_dec_ref(v_c_6549_);
lean_dec_ref(v_goal_6548_);
v_a_6744_ = lean_ctor_get(v___x_6681_, 0);
v_isSharedCheck_6751_ = !lean_is_exclusive(v___x_6681_);
if (v_isSharedCheck_6751_ == 0)
{
v___x_6746_ = v___x_6681_;
v_isShared_6747_ = v_isSharedCheck_6751_;
goto v_resetjp_6745_;
}
else
{
lean_inc(v_a_6744_);
lean_dec(v___x_6681_);
v___x_6746_ = lean_box(0);
v_isShared_6747_ = v_isSharedCheck_6751_;
goto v_resetjp_6745_;
}
v_resetjp_6745_:
{
lean_object* v___x_6749_; 
if (v_isShared_6747_ == 0)
{
v___x_6749_ = v___x_6746_;
goto v_reusejp_6748_;
}
else
{
lean_object* v_reuseFailAlloc_6750_; 
v_reuseFailAlloc_6750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_a_6744_);
v___x_6749_ = v_reuseFailAlloc_6750_;
goto v_reusejp_6748_;
}
v_reusejp_6748_:
{
return v___x_6749_;
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
lean_object* v_a_6760_; lean_object* v___x_6762_; uint8_t v_isShared_6763_; uint8_t v_isSharedCheck_6767_; 
lean_dec_ref(v___x_6574_);
lean_dec(v_a_6572_);
lean_dec(v_a_6570_);
lean_dec_ref(v_kp_6554_);
lean_dec_ref(v_c_6549_);
lean_dec_ref(v_goal_6548_);
v_a_6760_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6767_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6767_ == 0)
{
v___x_6762_ = v___x_6579_;
v_isShared_6763_ = v_isSharedCheck_6767_;
goto v_resetjp_6761_;
}
else
{
lean_inc(v_a_6760_);
lean_dec(v___x_6579_);
v___x_6762_ = lean_box(0);
v_isShared_6763_ = v_isSharedCheck_6767_;
goto v_resetjp_6761_;
}
v_resetjp_6761_:
{
lean_object* v___x_6765_; 
if (v_isShared_6763_ == 0)
{
v___x_6765_ = v___x_6762_;
goto v_reusejp_6764_;
}
else
{
lean_object* v_reuseFailAlloc_6766_; 
v_reuseFailAlloc_6766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6766_, 0, v_a_6760_);
v___x_6765_ = v_reuseFailAlloc_6766_;
goto v_reusejp_6764_;
}
v_reusejp_6764_:
{
return v___x_6765_;
}
}
}
}
else
{
lean_object* v_a_6768_; lean_object* v___x_6770_; uint8_t v_isShared_6771_; uint8_t v_isSharedCheck_6775_; 
lean_dec(v_a_6570_);
lean_dec_ref(v_kp_6554_);
lean_dec(v_candidates_x3f_6552_);
lean_dec(v_numCases_6550_);
lean_dec_ref(v_c_6549_);
lean_dec_ref(v_goal_6548_);
v_a_6768_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6775_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6775_ == 0)
{
v___x_6770_ = v___x_6571_;
v_isShared_6771_ = v_isSharedCheck_6775_;
goto v_resetjp_6769_;
}
else
{
lean_inc(v_a_6768_);
lean_dec(v___x_6571_);
v___x_6770_ = lean_box(0);
v_isShared_6771_ = v_isSharedCheck_6775_;
goto v_resetjp_6769_;
}
v_resetjp_6769_:
{
lean_object* v___x_6773_; 
if (v_isShared_6771_ == 0)
{
v___x_6773_ = v___x_6770_;
goto v_reusejp_6772_;
}
else
{
lean_object* v_reuseFailAlloc_6774_; 
v_reuseFailAlloc_6774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6774_, 0, v_a_6768_);
v___x_6773_ = v_reuseFailAlloc_6774_;
goto v_reusejp_6772_;
}
v_reusejp_6772_:
{
return v___x_6773_;
}
}
}
}
else
{
lean_object* v_a_6776_; lean_object* v___x_6778_; uint8_t v_isShared_6779_; uint8_t v_isSharedCheck_6783_; 
lean_dec_ref(v_kp_6554_);
lean_dec(v_candidates_x3f_6552_);
lean_dec(v_numCases_6550_);
lean_dec_ref(v_c_6549_);
lean_dec_ref(v_goal_6548_);
v_a_6776_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6783_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6783_ == 0)
{
v___x_6778_ = v___x_6569_;
v_isShared_6779_ = v_isSharedCheck_6783_;
goto v_resetjp_6777_;
}
else
{
lean_inc(v_a_6776_);
lean_dec(v___x_6569_);
v___x_6778_ = lean_box(0);
v_isShared_6779_ = v_isSharedCheck_6783_;
goto v_resetjp_6777_;
}
v_resetjp_6777_:
{
lean_object* v___x_6781_; 
if (v_isShared_6779_ == 0)
{
v___x_6781_ = v___x_6778_;
goto v_reusejp_6780_;
}
else
{
lean_object* v_reuseFailAlloc_6782_; 
v_reuseFailAlloc_6782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6782_, 0, v_a_6776_);
v___x_6781_ = v_reuseFailAlloc_6782_;
goto v_reusejp_6780_;
}
v_reusejp_6780_:
{
return v___x_6781_;
}
}
}
}
else
{
lean_object* v_a_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6791_; 
lean_dec_ref(v_kp_6554_);
lean_dec(v_candidates_x3f_6552_);
lean_dec(v_numCases_6550_);
lean_dec_ref(v_c_6549_);
lean_dec_ref(v_goal_6548_);
v_a_6784_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6791_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6791_ == 0)
{
v___x_6786_ = v___x_6566_;
v_isShared_6787_ = v_isSharedCheck_6791_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_a_6784_);
lean_dec(v___x_6566_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6791_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___x_6789_; 
if (v_isShared_6787_ == 0)
{
v___x_6789_ = v___x_6786_;
goto v_reusejp_6788_;
}
else
{
lean_object* v_reuseFailAlloc_6790_; 
v_reuseFailAlloc_6790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6790_, 0, v_a_6784_);
v___x_6789_ = v_reuseFailAlloc_6790_;
goto v_reusejp_6788_;
}
v_reusejp_6788_:
{
return v___x_6789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_goal_6792_ = _args[0];
lean_object* v_c_6793_ = _args[1];
lean_object* v_numCases_6794_ = _args[2];
lean_object* v_isRec_6795_ = _args[3];
lean_object* v_candidates_x3f_6796_ = _args[4];
lean_object* v_compress_6797_ = _args[5];
lean_object* v_kp_6798_ = _args[6];
lean_object* v_stopAtFirstFailure_6799_ = _args[7];
lean_object* v___y_6800_ = _args[8];
lean_object* v___y_6801_ = _args[9];
lean_object* v___y_6802_ = _args[10];
lean_object* v___y_6803_ = _args[11];
lean_object* v___y_6804_ = _args[12];
lean_object* v___y_6805_ = _args[13];
lean_object* v___y_6806_ = _args[14];
lean_object* v___y_6807_ = _args[15];
lean_object* v___y_6808_ = _args[16];
lean_object* v___y_6809_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6810_; uint8_t v_compress_boxed_6811_; uint8_t v_stopAtFirstFailure_boxed_6812_; lean_object* v_res_6813_; 
v_isRec_boxed_6810_ = lean_unbox(v_isRec_6795_);
v_compress_boxed_6811_ = lean_unbox(v_compress_6797_);
v_stopAtFirstFailure_boxed_6812_ = lean_unbox(v_stopAtFirstFailure_6799_);
v_res_6813_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3(v_goal_6792_, v_c_6793_, v_numCases_6794_, v_isRec_boxed_6810_, v_candidates_x3f_6796_, v_compress_boxed_6811_, v_kp_6798_, v_stopAtFirstFailure_boxed_6812_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
lean_dec(v___y_6808_);
lean_dec_ref(v___y_6807_);
lean_dec(v___y_6806_);
lean_dec_ref(v___y_6805_);
lean_dec(v___y_6804_);
lean_dec_ref(v___y_6803_);
lean_dec(v___y_6802_);
lean_dec_ref(v___y_6801_);
lean_dec(v___y_6800_);
return v_res_6813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_6814_, lean_object* v_numCases_6815_, uint8_t v_isRec_6816_, uint8_t v_stopAtFirstFailure_6817_, uint8_t v_compress_6818_, lean_object* v_candidates_x3f_6819_, lean_object* v_goal_6820_, lean_object* v_kp_6821_, lean_object* v_a_6822_, lean_object* v_a_6823_, lean_object* v_a_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_, lean_object* v_a_6830_){
_start:
{
lean_object* v___x_6832_; lean_object* v___x_6833_; lean_object* v___x_6834_; lean_object* v___f_6835_; lean_object* v___x_6836_; 
v___x_6832_ = lean_box(v_isRec_6816_);
v___x_6833_ = lean_box(v_compress_6818_);
v___x_6834_ = lean_box(v_stopAtFirstFailure_6817_);
lean_inc_ref(v_goal_6820_);
v___f_6835_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__3___boxed), 18, 8);
lean_closure_set(v___f_6835_, 0, v_goal_6820_);
lean_closure_set(v___f_6835_, 1, v_c_6814_);
lean_closure_set(v___f_6835_, 2, v_numCases_6815_);
lean_closure_set(v___f_6835_, 3, v___x_6832_);
lean_closure_set(v___f_6835_, 4, v_candidates_x3f_6819_);
lean_closure_set(v___f_6835_, 5, v___x_6833_);
lean_closure_set(v___f_6835_, 6, v_kp_6821_);
lean_closure_set(v___f_6835_, 7, v___x_6834_);
v___x_6836_ = l_Lean_Meta_Grind_withHoistedDecls___redArg(v_goal_6820_, v___f_6835_, v_a_6822_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_);
return v___x_6836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6837_ = _args[0];
lean_object* v_numCases_6838_ = _args[1];
lean_object* v_isRec_6839_ = _args[2];
lean_object* v_stopAtFirstFailure_6840_ = _args[3];
lean_object* v_compress_6841_ = _args[4];
lean_object* v_candidates_x3f_6842_ = _args[5];
lean_object* v_goal_6843_ = _args[6];
lean_object* v_kp_6844_ = _args[7];
lean_object* v_a_6845_ = _args[8];
lean_object* v_a_6846_ = _args[9];
lean_object* v_a_6847_ = _args[10];
lean_object* v_a_6848_ = _args[11];
lean_object* v_a_6849_ = _args[12];
lean_object* v_a_6850_ = _args[13];
lean_object* v_a_6851_ = _args[14];
lean_object* v_a_6852_ = _args[15];
lean_object* v_a_6853_ = _args[16];
lean_object* v_a_6854_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6855_; uint8_t v_stopAtFirstFailure_boxed_6856_; uint8_t v_compress_boxed_6857_; lean_object* v_res_6858_; 
v_isRec_boxed_6855_ = lean_unbox(v_isRec_6839_);
v_stopAtFirstFailure_boxed_6856_ = lean_unbox(v_stopAtFirstFailure_6840_);
v_compress_boxed_6857_ = lean_unbox(v_compress_6841_);
v_res_6858_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6837_, v_numCases_6838_, v_isRec_boxed_6855_, v_stopAtFirstFailure_boxed_6856_, v_compress_boxed_6857_, v_candidates_x3f_6842_, v_goal_6843_, v_kp_6844_, v_a_6845_, v_a_6846_, v_a_6847_, v_a_6848_, v_a_6849_, v_a_6850_, v_a_6851_, v_a_6852_, v_a_6853_);
lean_dec(v_a_6853_);
lean_dec_ref(v_a_6852_);
lean_dec(v_a_6851_);
lean_dec_ref(v_a_6850_);
lean_dec(v_a_6849_);
lean_dec_ref(v_a_6848_);
lean_dec(v_a_6847_);
lean_dec_ref(v_a_6846_);
lean_dec(v_a_6845_);
return v_res_6858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6859_, lean_object* v_numCases_6860_, uint8_t v_isRec_6861_, uint8_t v_stopAtFirstFailure_6862_, uint8_t v_compress_6863_, lean_object* v_candidates_x3f_6864_, lean_object* v_goal_6865_, lean_object* v_x_6866_, lean_object* v_kp_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_){
_start:
{
lean_object* v___x_6878_; 
v___x_6878_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6859_, v_numCases_6860_, v_isRec_6861_, v_stopAtFirstFailure_6862_, v_compress_6863_, v_candidates_x3f_6864_, v_goal_6865_, v_kp_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_);
return v___x_6878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6879_ = _args[0];
lean_object* v_numCases_6880_ = _args[1];
lean_object* v_isRec_6881_ = _args[2];
lean_object* v_stopAtFirstFailure_6882_ = _args[3];
lean_object* v_compress_6883_ = _args[4];
lean_object* v_candidates_x3f_6884_ = _args[5];
lean_object* v_goal_6885_ = _args[6];
lean_object* v_x_6886_ = _args[7];
lean_object* v_kp_6887_ = _args[8];
lean_object* v_a_6888_ = _args[9];
lean_object* v_a_6889_ = _args[10];
lean_object* v_a_6890_ = _args[11];
lean_object* v_a_6891_ = _args[12];
lean_object* v_a_6892_ = _args[13];
lean_object* v_a_6893_ = _args[14];
lean_object* v_a_6894_ = _args[15];
lean_object* v_a_6895_ = _args[16];
lean_object* v_a_6896_ = _args[17];
lean_object* v_a_6897_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6898_; uint8_t v_stopAtFirstFailure_boxed_6899_; uint8_t v_compress_boxed_6900_; lean_object* v_res_6901_; 
v_isRec_boxed_6898_ = lean_unbox(v_isRec_6881_);
v_stopAtFirstFailure_boxed_6899_ = lean_unbox(v_stopAtFirstFailure_6882_);
v_compress_boxed_6900_ = lean_unbox(v_compress_6883_);
v_res_6901_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6879_, v_numCases_6880_, v_isRec_boxed_6898_, v_stopAtFirstFailure_boxed_6899_, v_compress_boxed_6900_, v_candidates_x3f_6884_, v_goal_6885_, v_x_6886_, v_kp_6887_, v_a_6888_, v_a_6889_, v_a_6890_, v_a_6891_, v_a_6892_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_);
lean_dec(v_a_6896_);
lean_dec_ref(v_a_6895_);
lean_dec(v_a_6894_);
lean_dec_ref(v_a_6893_);
lean_dec(v_a_6892_);
lean_dec_ref(v_a_6891_);
lean_dec(v_a_6890_);
lean_dec_ref(v_a_6889_);
lean_dec(v_a_6888_);
lean_dec_ref(v_x_6886_);
return v_res_6901_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_6902_, lean_object* v_a_6903_, lean_object* v_goal_6904_, lean_object* v___x_6905_, lean_object* v_snd_6906_, lean_object* v___x_6907_, uint8_t v_stopAtFirstFailure_6908_, lean_object* v___x_6909_, lean_object* v_as_6910_, lean_object* v_as_x27_6911_, lean_object* v_b_6912_, lean_object* v_a_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_){
_start:
{
lean_object* v___x_6924_; 
v___x_6924_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6902_, v_a_6903_, v_goal_6904_, v___x_6905_, v_snd_6906_, v___x_6907_, v_stopAtFirstFailure_6908_, v___x_6909_, v_as_x27_6911_, v_b_6912_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_);
return v___x_6924_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6925_ = _args[0];
lean_object* v_a_6926_ = _args[1];
lean_object* v_goal_6927_ = _args[2];
lean_object* v___x_6928_ = _args[3];
lean_object* v_snd_6929_ = _args[4];
lean_object* v___x_6930_ = _args[5];
lean_object* v_stopAtFirstFailure_6931_ = _args[6];
lean_object* v___x_6932_ = _args[7];
lean_object* v_as_6933_ = _args[8];
lean_object* v_as_x27_6934_ = _args[9];
lean_object* v_b_6935_ = _args[10];
lean_object* v_a_6936_ = _args[11];
lean_object* v___y_6937_ = _args[12];
lean_object* v___y_6938_ = _args[13];
lean_object* v___y_6939_ = _args[14];
lean_object* v___y_6940_ = _args[15];
lean_object* v___y_6941_ = _args[16];
lean_object* v___y_6942_ = _args[17];
lean_object* v___y_6943_ = _args[18];
lean_object* v___y_6944_ = _args[19];
lean_object* v___y_6945_ = _args[20];
lean_object* v___y_6946_ = _args[21];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6947_; lean_object* v_res_6948_; 
v_stopAtFirstFailure_boxed_6947_ = lean_unbox(v_stopAtFirstFailure_6931_);
v_res_6948_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6925_, v_a_6926_, v_goal_6927_, v___x_6928_, v_snd_6929_, v___x_6930_, v_stopAtFirstFailure_boxed_6947_, v___x_6932_, v_as_6933_, v_as_x27_6934_, v_b_6935_, v_a_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_);
lean_dec(v___y_6945_);
lean_dec_ref(v___y_6944_);
lean_dec(v___y_6943_);
lean_dec_ref(v___y_6942_);
lean_dec(v___y_6941_);
lean_dec_ref(v___y_6940_);
lean_dec(v___y_6939_);
lean_dec_ref(v___y_6938_);
lean_dec(v___y_6937_);
lean_dec(v_as_x27_6934_);
lean_dec(v_as_6933_);
lean_dec_ref(v___x_6932_);
lean_dec(v___x_6928_);
return v_res_6948_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_mvarId_6949_, lean_object* v_val_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_){
_start:
{
lean_object* v___x_6961_; 
v___x_6961_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_mvarId_6949_, v_val_6950_, v___y_6957_);
return v___x_6961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_mvarId_6962_, lean_object* v_val_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_, lean_object* v___y_6971_, lean_object* v___y_6972_, lean_object* v___y_6973_){
_start:
{
lean_object* v_res_6974_; 
v_res_6974_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_mvarId_6962_, v_val_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_, v___y_6971_, v___y_6972_);
lean_dec(v___y_6972_);
lean_dec_ref(v___y_6971_);
lean_dec(v___y_6970_);
lean_dec_ref(v___y_6969_);
lean_dec(v___y_6968_);
lean_dec_ref(v___y_6967_);
lean_dec(v___y_6966_);
lean_dec_ref(v___y_6965_);
lean_dec(v___y_6964_);
return v_res_6974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4(lean_object* v_00_u03b2_6975_, lean_object* v_x_6976_, lean_object* v_x_6977_, lean_object* v_x_6978_){
_start:
{
lean_object* v___x_6979_; 
v___x_6979_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4___redArg(v_x_6976_, v_x_6977_, v_x_6978_);
return v___x_6979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(lean_object* v_00_u03b2_6980_, lean_object* v_x_6981_, size_t v_x_6982_, size_t v_x_6983_, lean_object* v_x_6984_, lean_object* v_x_6985_){
_start:
{
lean_object* v___x_6986_; 
v___x_6986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___redArg(v_x_6981_, v_x_6982_, v_x_6983_, v_x_6984_, v_x_6985_);
return v___x_6986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b2_6987_, lean_object* v_x_6988_, lean_object* v_x_6989_, lean_object* v_x_6990_, lean_object* v_x_6991_, lean_object* v_x_6992_){
_start:
{
size_t v_x_119196__boxed_6993_; size_t v_x_119197__boxed_6994_; lean_object* v_res_6995_; 
v_x_119196__boxed_6993_ = lean_unbox_usize(v_x_6989_);
lean_dec(v_x_6989_);
v_x_119197__boxed_6994_ = lean_unbox_usize(v_x_6990_);
lean_dec(v_x_6990_);
v_res_6995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5(v_00_u03b2_6987_, v_x_6988_, v_x_119196__boxed_6993_, v_x_119197__boxed_6994_, v_x_6991_, v_x_6992_);
return v_res_6995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_6996_, lean_object* v_n_6997_, lean_object* v_k_6998_, lean_object* v_v_6999_){
_start:
{
lean_object* v___x_7000_; 
v___x_7000_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6___redArg(v_n_6997_, v_k_6998_, v_v_6999_);
return v___x_7000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_7001_, size_t v_depth_7002_, lean_object* v_keys_7003_, lean_object* v_vals_7004_, lean_object* v_heq_7005_, lean_object* v_i_7006_, lean_object* v_entries_7007_){
_start:
{
lean_object* v___x_7008_; 
v___x_7008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___redArg(v_depth_7002_, v_keys_7003_, v_vals_7004_, v_i_7006_, v_entries_7007_);
return v___x_7008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_7009_, lean_object* v_depth_7010_, lean_object* v_keys_7011_, lean_object* v_vals_7012_, lean_object* v_heq_7013_, lean_object* v_i_7014_, lean_object* v_entries_7015_){
_start:
{
size_t v_depth_boxed_7016_; lean_object* v_res_7017_; 
v_depth_boxed_7016_ = lean_unbox_usize(v_depth_7010_);
lean_dec(v_depth_7010_);
v_res_7017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__7(v_00_u03b2_7009_, v_depth_boxed_7016_, v_keys_7011_, v_vals_7012_, v_heq_7013_, v_i_7014_, v_entries_7015_);
lean_dec_ref(v_vals_7012_);
lean_dec_ref(v_keys_7011_);
return v_res_7017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_7018_, lean_object* v_x_7019_, lean_object* v_x_7020_, lean_object* v_x_7021_, lean_object* v_x_7022_){
_start:
{
lean_object* v___x_7023_; 
v___x_7023_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__4_spec__4_spec__5_spec__6_spec__7___redArg(v_x_7019_, v_x_7020_, v_x_7021_, v_x_7022_);
return v___x_7023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_7024_, lean_object* v___y_7025_, lean_object* v___y_7026_, lean_object* v___y_7027_, lean_object* v___y_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_, lean_object* v___y_7032_, lean_object* v___y_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_){
_start:
{
lean_object* v___x_7037_; 
v___x_7037_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_7024_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_, v___y_7032_, v___y_7033_, v___y_7034_, v___y_7035_);
return v___x_7037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_, lean_object* v___y_7042_, lean_object* v___y_7043_, lean_object* v___y_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_){
_start:
{
lean_object* v_res_7051_; 
v_res_7051_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_);
lean_dec(v___y_7049_);
lean_dec_ref(v___y_7048_);
lean_dec(v___y_7047_);
lean_dec_ref(v___y_7046_);
lean_dec(v___y_7045_);
lean_dec_ref(v___y_7044_);
lean_dec(v___y_7043_);
lean_dec_ref(v___y_7042_);
lean_dec(v___y_7041_);
lean_dec_ref(v___y_7039_);
return v_res_7051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_, lean_object* v___y_7058_, lean_object* v___y_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_){
_start:
{
lean_object* v___x_7063_; lean_object* v___x_7064_; 
v___x_7063_ = lean_st_mk_ref(v_goal_7052_);
v___x_7064_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_7063_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_, v___y_7057_, v___y_7058_, v___y_7059_, v___y_7060_, v___y_7061_);
if (lean_obj_tag(v___x_7064_) == 0)
{
lean_object* v_a_7065_; lean_object* v___x_7067_; uint8_t v_isShared_7068_; uint8_t v_isSharedCheck_7074_; 
v_a_7065_ = lean_ctor_get(v___x_7064_, 0);
v_isSharedCheck_7074_ = !lean_is_exclusive(v___x_7064_);
if (v_isSharedCheck_7074_ == 0)
{
v___x_7067_ = v___x_7064_;
v_isShared_7068_ = v_isSharedCheck_7074_;
goto v_resetjp_7066_;
}
else
{
lean_inc(v_a_7065_);
lean_dec(v___x_7064_);
v___x_7067_ = lean_box(0);
v_isShared_7068_ = v_isSharedCheck_7074_;
goto v_resetjp_7066_;
}
v_resetjp_7066_:
{
lean_object* v___x_7069_; lean_object* v___x_7070_; lean_object* v___x_7072_; 
v___x_7069_ = lean_st_ref_get(v___x_7063_);
lean_dec(v___x_7063_);
v___x_7070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7070_, 0, v_a_7065_);
lean_ctor_set(v___x_7070_, 1, v___x_7069_);
if (v_isShared_7068_ == 0)
{
lean_ctor_set(v___x_7067_, 0, v___x_7070_);
v___x_7072_ = v___x_7067_;
goto v_reusejp_7071_;
}
else
{
lean_object* v_reuseFailAlloc_7073_; 
v_reuseFailAlloc_7073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7073_, 0, v___x_7070_);
v___x_7072_ = v_reuseFailAlloc_7073_;
goto v_reusejp_7071_;
}
v_reusejp_7071_:
{
return v___x_7072_;
}
}
}
else
{
lean_object* v_a_7075_; lean_object* v___x_7077_; uint8_t v_isShared_7078_; uint8_t v_isSharedCheck_7082_; 
lean_dec(v___x_7063_);
v_a_7075_ = lean_ctor_get(v___x_7064_, 0);
v_isSharedCheck_7082_ = !lean_is_exclusive(v___x_7064_);
if (v_isSharedCheck_7082_ == 0)
{
v___x_7077_ = v___x_7064_;
v_isShared_7078_ = v_isSharedCheck_7082_;
goto v_resetjp_7076_;
}
else
{
lean_inc(v_a_7075_);
lean_dec(v___x_7064_);
v___x_7077_ = lean_box(0);
v_isShared_7078_ = v_isSharedCheck_7082_;
goto v_resetjp_7076_;
}
v_resetjp_7076_:
{
lean_object* v___x_7080_; 
if (v_isShared_7078_ == 0)
{
v___x_7080_ = v___x_7077_;
goto v_reusejp_7079_;
}
else
{
lean_object* v_reuseFailAlloc_7081_; 
v_reuseFailAlloc_7081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_a_7075_);
v___x_7080_ = v_reuseFailAlloc_7081_;
goto v_reusejp_7079_;
}
v_reusejp_7079_:
{
return v___x_7080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_, lean_object* v___y_7092_, lean_object* v___y_7093_){
_start:
{
lean_object* v_res_7094_; 
v_res_7094_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_, v___y_7088_, v___y_7089_, v___y_7090_, v___y_7091_, v___y_7092_);
lean_dec(v___y_7092_);
lean_dec_ref(v___y_7091_);
lean_dec(v___y_7090_);
lean_dec_ref(v___y_7089_);
lean_dec(v___y_7088_);
lean_dec_ref(v___y_7087_);
lean_dec(v___y_7086_);
lean_dec_ref(v___y_7085_);
lean_dec(v___y_7084_);
return v_res_7094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_7095_, lean_object* v___f_7096_, lean_object* v___y_7097_, lean_object* v___y_7098_, lean_object* v___y_7099_, lean_object* v___y_7100_, lean_object* v___y_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_, lean_object* v___y_7105_, lean_object* v___y_7106_, lean_object* v___y_7107_, lean_object* v___y_7108_){
_start:
{
lean_object* v___x_7110_; lean_object* v___x_7111_; 
v___x_7110_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_7110_, 0, v___y_7095_);
v___x_7111_ = l_Lean_Meta_Grind_Action_andThen(v___x_7110_, v___f_7096_, v___y_7097_, v___y_7098_, v___y_7099_, v___y_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_);
return v___x_7111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_7112_, lean_object* v___f_7113_, lean_object* v___y_7114_, lean_object* v___y_7115_, lean_object* v___y_7116_, lean_object* v___y_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_, lean_object* v___y_7120_, lean_object* v___y_7121_, lean_object* v___y_7122_, lean_object* v___y_7123_, lean_object* v___y_7124_, lean_object* v___y_7125_, lean_object* v___y_7126_){
_start:
{
lean_object* v_res_7127_; 
v_res_7127_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_7112_, v___f_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_, v___y_7124_, v___y_7125_);
lean_dec(v___y_7125_);
lean_dec_ref(v___y_7124_);
lean_dec(v___y_7123_);
lean_dec_ref(v___y_7122_);
lean_dec(v___y_7121_);
lean_dec_ref(v___y_7120_);
lean_dec(v___y_7119_);
lean_dec_ref(v___y_7118_);
lean_dec(v___y_7117_);
return v_res_7127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_7129_, uint8_t v_compress_7130_, lean_object* v_goal_7131_, lean_object* v_kna_7132_, lean_object* v_kp_7133_, lean_object* v_a_7134_, lean_object* v_a_7135_, lean_object* v_a_7136_, lean_object* v_a_7137_, lean_object* v_a_7138_, lean_object* v_a_7139_, lean_object* v_a_7140_, lean_object* v_a_7141_, lean_object* v_a_7142_){
_start:
{
lean_object* v_toGoalState_7144_; lean_object* v_split_7145_; lean_object* v_mvarId_7146_; lean_object* v_candidates_7147_; lean_object* v___f_7148_; lean_object* v___f_7149_; lean_object* v___x_7150_; 
v_toGoalState_7144_ = lean_ctor_get(v_goal_7131_, 0);
v_split_7145_ = lean_ctor_get(v_toGoalState_7144_, 15);
v_mvarId_7146_ = lean_ctor_get(v_goal_7131_, 1);
lean_inc(v_mvarId_7146_);
v_candidates_7147_ = lean_ctor_get(v_split_7145_, 0);
lean_inc(v_candidates_7147_);
v___f_7148_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_7149_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_7149_, 0, v_goal_7131_);
v___x_7150_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_mvarId_7146_, v___f_7149_, v_a_7134_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_, v_a_7141_, v_a_7142_);
if (lean_obj_tag(v___x_7150_) == 0)
{
lean_object* v_a_7151_; lean_object* v_fst_7152_; 
v_a_7151_ = lean_ctor_get(v___x_7150_, 0);
lean_inc(v_a_7151_);
lean_dec_ref_known(v___x_7150_, 1);
v_fst_7152_ = lean_ctor_get(v_a_7151_, 0);
if (lean_obj_tag(v_fst_7152_) == 1)
{
lean_object* v_snd_7153_; lean_object* v_c_7154_; lean_object* v_numCases_7155_; uint8_t v_isRec_7156_; lean_object* v___y_7158_; lean_object* v___x_7166_; lean_object* v___x_7167_; lean_object* v___x_7168_; uint8_t v___x_7171_; 
lean_inc_ref(v_fst_7152_);
v_snd_7153_ = lean_ctor_get(v_a_7151_, 1);
lean_inc(v_snd_7153_);
lean_dec(v_a_7151_);
v_c_7154_ = lean_ctor_get(v_fst_7152_, 0);
lean_inc_ref(v_c_7154_);
v_numCases_7155_ = lean_ctor_get(v_fst_7152_, 1);
lean_inc(v_numCases_7155_);
v_isRec_7156_ = lean_ctor_get_uint8(v_fst_7152_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_7152_, 2);
v___x_7166_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_7154_);
v___x_7167_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_7153_, v___x_7166_);
lean_dec_ref(v___x_7166_);
v___x_7168_ = lean_unsigned_to_nat(1u);
v___x_7171_ = lean_nat_dec_lt(v___x_7168_, v_numCases_7155_);
if (v___x_7171_ == 0)
{
if (v_isRec_7156_ == 0)
{
v___y_7158_ = v___x_7167_;
goto v___jp_7157_;
}
else
{
goto v___jp_7169_;
}
}
else
{
goto v___jp_7169_;
}
v___jp_7157_:
{
lean_object* v___f_7159_; lean_object* v___x_7160_; lean_object* v___x_7161_; lean_object* v___x_7162_; lean_object* v___x_7163_; lean_object* v___x_7164_; lean_object* v___x_7165_; 
v___f_7159_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_7159_, 0, v___y_7158_);
lean_closure_set(v___f_7159_, 1, v___f_7148_);
v___x_7160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7160_, 0, v_candidates_7147_);
v___x_7161_ = lean_box(v_isRec_7156_);
v___x_7162_ = lean_box(v_stopAtFirstFailure_7129_);
v___x_7163_ = lean_box(v_compress_7130_);
v___x_7164_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_7164_, 0, v_c_7154_);
lean_closure_set(v___x_7164_, 1, v_numCases_7155_);
lean_closure_set(v___x_7164_, 2, v___x_7161_);
lean_closure_set(v___x_7164_, 3, v___x_7162_);
lean_closure_set(v___x_7164_, 4, v___x_7163_);
lean_closure_set(v___x_7164_, 5, v___x_7160_);
v___x_7165_ = l_Lean_Meta_Grind_Action_andThen(v___x_7164_, v___f_7159_, v_snd_7153_, v_kna_7132_, v_kp_7133_, v_a_7134_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_, v_a_7141_, v_a_7142_);
return v___x_7165_;
}
v___jp_7169_:
{
lean_object* v___x_7170_; 
v___x_7170_ = lean_nat_add(v___x_7167_, v___x_7168_);
lean_dec(v___x_7167_);
v___y_7158_ = v___x_7170_;
goto v___jp_7157_;
}
}
else
{
lean_object* v_snd_7172_; lean_object* v___x_7173_; 
lean_dec(v_candidates_7147_);
lean_dec_ref(v_kp_7133_);
v_snd_7172_ = lean_ctor_get(v_a_7151_, 1);
lean_inc(v_snd_7172_);
lean_dec(v_a_7151_);
lean_inc(v_a_7142_);
lean_inc_ref(v_a_7141_);
lean_inc(v_a_7140_);
lean_inc_ref(v_a_7139_);
lean_inc(v_a_7138_);
lean_inc_ref(v_a_7137_);
lean_inc(v_a_7136_);
lean_inc_ref(v_a_7135_);
lean_inc(v_a_7134_);
v___x_7173_ = lean_apply_11(v_kna_7132_, v_snd_7172_, v_a_7134_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_, v_a_7141_, v_a_7142_, lean_box(0));
return v___x_7173_;
}
}
else
{
lean_object* v_a_7174_; lean_object* v___x_7176_; uint8_t v_isShared_7177_; uint8_t v_isSharedCheck_7181_; 
lean_dec(v_candidates_7147_);
lean_dec_ref(v_kp_7133_);
lean_dec_ref(v_kna_7132_);
v_a_7174_ = lean_ctor_get(v___x_7150_, 0);
v_isSharedCheck_7181_ = !lean_is_exclusive(v___x_7150_);
if (v_isSharedCheck_7181_ == 0)
{
v___x_7176_ = v___x_7150_;
v_isShared_7177_ = v_isSharedCheck_7181_;
goto v_resetjp_7175_;
}
else
{
lean_inc(v_a_7174_);
lean_dec(v___x_7150_);
v___x_7176_ = lean_box(0);
v_isShared_7177_ = v_isSharedCheck_7181_;
goto v_resetjp_7175_;
}
v_resetjp_7175_:
{
lean_object* v___x_7179_; 
if (v_isShared_7177_ == 0)
{
v___x_7179_ = v___x_7176_;
goto v_reusejp_7178_;
}
else
{
lean_object* v_reuseFailAlloc_7180_; 
v_reuseFailAlloc_7180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7180_, 0, v_a_7174_);
v___x_7179_ = v_reuseFailAlloc_7180_;
goto v_reusejp_7178_;
}
v_reusejp_7178_:
{
return v___x_7179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_7182_, lean_object* v_compress_7183_, lean_object* v_goal_7184_, lean_object* v_kna_7185_, lean_object* v_kp_7186_, lean_object* v_a_7187_, lean_object* v_a_7188_, lean_object* v_a_7189_, lean_object* v_a_7190_, lean_object* v_a_7191_, lean_object* v_a_7192_, lean_object* v_a_7193_, lean_object* v_a_7194_, lean_object* v_a_7195_, lean_object* v_a_7196_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_7197_; uint8_t v_compress_boxed_7198_; lean_object* v_res_7199_; 
v_stopAtFirstFailure_boxed_7197_ = lean_unbox(v_stopAtFirstFailure_7182_);
v_compress_boxed_7198_ = lean_unbox(v_compress_7183_);
v_res_7199_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_7197_, v_compress_boxed_7198_, v_goal_7184_, v_kna_7185_, v_kp_7186_, v_a_7187_, v_a_7188_, v_a_7189_, v_a_7190_, v_a_7191_, v_a_7192_, v_a_7193_, v_a_7194_, v_a_7195_);
lean_dec(v_a_7195_);
lean_dec_ref(v_a_7194_);
lean_dec(v_a_7193_);
lean_dec_ref(v_a_7192_);
lean_dec(v_a_7191_);
lean_dec_ref(v_a_7190_);
lean_dec(v_a_7189_);
lean_dec_ref(v_a_7188_);
lean_dec(v_a_7187_);
return v_res_7199_;
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
