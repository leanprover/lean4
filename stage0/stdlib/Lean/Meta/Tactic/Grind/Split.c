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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_Goal_setIntroBase(lean_object*, uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getHoistedDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkHoistedDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 82, 43, 49, 91, 105, 112, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", generation: "};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_resolved_863_ = lean_ctor_get(v_split_862_, 3);
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
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
lean_ctor_set(v___x_1070_, 4, v___x_1068_);
lean_ctor_set(v___x_1070_, 5, v___x_1068_);
lean_ctor_set(v___x_1070_, 6, v___x_1068_);
lean_ctor_set(v___x_1070_, 7, v___x_1068_);
lean_ctor_set(v___x_1070_, 8, v___x_1068_);
lean_ctor_set(v___x_1070_, 9, v___x_1068_);
lean_ctor_set(v___x_1070_, 10, v___x_1068_);
lean_ctor_set(v___x_1070_, 11, v___x_1067_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(32u);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((size_t)5ULL);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_unsigned_to_nat(32u);
v___x_1077_ = lean_mk_empty_array_with_capacity(v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1079_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1075_);
lean_ctor_set(v___x_1079_, 3, v___x_1075_);
lean_ctor_set_usize(v___x_1079_, 4, v___x_1074_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(1);
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v___x_1080_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1105_, lean_object* v_declHint_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_env_1111_; uint8_t v___x_1112_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_st_ref_get(v___y_1107_);
v_env_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_Name_isAnonymous(v_declHint_1106_);
if (v___x_1112_ == 0)
{
uint8_t v_isExporting_1113_; 
v_isExporting_1113_ = lean_ctor_get_uint8(v_env_1111_, sizeof(void*)*13);
if (v_isExporting_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_msg_1105_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
lean_inc_ref(v_env_1111_);
v___x_1115_ = l_Lean_Environment_setExporting(v_env_1111_, v___x_1112_);
lean_inc(v_declHint_1106_);
lean_inc_ref(v___x_1115_);
v___x_1116_ = l_Lean_Environment_contains(v___x_1115_, v_declHint_1106_, v_isExporting_1113_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_msg_1105_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_c_1123_; lean_object* v___x_1124_; 
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1120_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1115_);
v___x_1121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1115_);
lean_ctor_set(v___x_1121_, 1, v___x_1118_);
lean_ctor_set(v___x_1121_, 2, v___x_1119_);
lean_ctor_set(v___x_1121_, 3, v___x_1120_);
lean_inc(v_declHint_1106_);
v___x_1122_ = l_Lean_MessageData_ofConstName(v_declHint_1106_, v___x_1112_);
v_c_1123_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1123_, 0, v___x_1121_);
lean_ctor_set(v_c_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1115_, v_declHint_1106_);
lean_dec_ref(v___x_1115_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1125_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v_c_1123_);
v___x_1127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_note(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_msg_1105_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1166_; 
v_val_1132_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1134_ = v___x_1124_;
v_isShared_1135_ = v_isSharedCheck_1166_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_dec(v___x_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1166_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v_moduleNames_1137_; lean_object* v_mod_1138_; uint8_t v___x_1139_; 
v___x_1136_ = l_Lean_Environment_header(v_env_1111_);
lean_dec_ref(v_env_1111_);
v_moduleNames_1137_ = lean_ctor_get(v___x_1136_, 4);
lean_inc_ref(v_moduleNames_1137_);
lean_dec_ref(v___x_1136_);
v_mod_1138_ = lean_array_get(v___x_1109_, v_moduleNames_1137_, v_val_1132_);
lean_dec(v_val_1132_);
lean_dec_ref(v_moduleNames_1137_);
v___x_1139_ = l_Lean_isPrivateName(v_declHint_1106_);
lean_dec(v_declHint_1106_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_c_1123_);
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_ofName(v_mod_1138_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_note(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_msg_1105_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1149_);
v___x_1151_ = v___x_1134_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v_c_1123_);
v___x_1155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_MessageData_ofName(v_mod_1138_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_MessageData_note(v___x_1160_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_msg_1105_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1162_);
v___x_1164_ = v___x_1134_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1167_; 
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_msg_1105_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1168_, lean_object* v_declHint_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1168_, v_declHint_1169_, v___y_1170_);
lean_dec(v___y_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1196_; 
v___x_1186_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1173_, v_declHint_1174_, v___y_1184_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = l_Lean_unknownIdentifierMessageTag;
v___x_1192_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1197_, lean_object* v_declHint_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1197_, v_declHint_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_env_1218_; uint8_t v___x_1219_; lean_object* v_env_1220_; lean_object* v___x_1221_; lean_object* v_toCold_1222_; lean_object* v_mctx_1223_; lean_object* v_lctx_1224_; lean_object* v_options_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1217_ = lean_st_ref_get(v___y_1215_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_env_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = 0;
v_env_1220_ = l_Lean_Environment_setRecordingDeps(v_env_1218_, v___x_1219_);
v___x_1221_ = lean_st_ref_get(v___y_1213_);
v_toCold_1222_ = lean_ctor_get(v___y_1214_, 0);
v_mctx_1223_ = lean_ctor_get(v___x_1221_, 0);
lean_inc_ref(v_mctx_1223_);
lean_dec(v___x_1221_);
v_lctx_1224_ = lean_ctor_get(v___y_1212_, 2);
v_options_1225_ = lean_ctor_get(v_toCold_1222_, 2);
lean_inc_ref(v_options_1225_);
lean_inc_ref(v_lctx_1224_);
v___x_1226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1226_, 0, v_env_1220_);
lean_ctor_set(v___x_1226_, 1, v_mctx_1223_);
lean_ctor_set(v___x_1226_, 2, v_lctx_1224_);
lean_ctor_set(v___x_1226_, 3, v_options_1225_);
v___x_1227_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_msgData_1211_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_ref_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
v_ref_1242_ = lean_ctor_get(v___y_1239_, 2);
v___x_1243_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_inc(v_ref_1242_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_ref_1242_);
lean_ctor_set(v___x_1248_, 1, v_a_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 0, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1260_, lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_toCold_1273_; lean_object* v_currRecDepth_1274_; lean_object* v_ref_1275_; uint16_t v_optionFlags_1276_; uint8_t v_suppressElabErrors_1277_; uint8_t v_checkDeprecated_1278_; uint8_t v_isRecordingDeps_1279_; lean_object* v_ref_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_toCold_1273_ = lean_ctor_get(v___y_1270_, 0);
v_currRecDepth_1274_ = lean_ctor_get(v___y_1270_, 1);
v_ref_1275_ = lean_ctor_get(v___y_1270_, 2);
v_optionFlags_1276_ = lean_ctor_get_uint16(v___y_1270_, sizeof(void*)*3);
v_suppressElabErrors_1277_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 2);
v_checkDeprecated_1278_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1279_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 4);
v_ref_1280_ = l_Lean_replaceRef(v_ref_1260_, v_ref_1275_);
lean_inc(v_currRecDepth_1274_);
lean_inc_ref(v_toCold_1273_);
v___x_1281_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1281_, 0, v_toCold_1273_);
lean_ctor_set(v___x_1281_, 1, v_currRecDepth_1274_);
lean_ctor_set(v___x_1281_, 2, v_ref_1280_);
lean_ctor_set_uint16(v___x_1281_, sizeof(void*)*3, v_optionFlags_1276_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 2, v_suppressElabErrors_1277_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 3, v_checkDeprecated_1278_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 4, v_isRecordingDeps_1279_);
v___x_1282_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1261_, v___y_1268_, v___y_1269_, v___x_1281_, v___y_1271_);
lean_dec_ref_known(v___x_1281_, 3);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1283_, v_msg_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v_ref_1283_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1297_, lean_object* v_msg_1298_, lean_object* v_declHint_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_a_1312_; lean_object* v___x_1313_; 
v___x_1311_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1298_, v_declHint_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1297_, v_a_1312_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1314_, lean_object* v_msg_1315_, lean_object* v_declHint_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1314_, v_msg_1315_, v_declHint_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v_ref_1314_);
return v_res_1328_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1335_, lean_object* v_constName_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1348_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1349_ = 0;
lean_inc(v_constName_1336_);
v___x_1350_ = l_Lean_MessageData_ofConstName(v_constName_1336_, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1348_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1335_, v___x_1353_, v_constName_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1355_, lean_object* v_constName_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1355_, v_constName_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v_ref_1355_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_ref_1381_; lean_object* v___x_1382_; 
v_ref_1381_ = lean_ctor_get(v___y_1378_, 2);
v___x_1382_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1381_, v_constName_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v_env_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_st_ref_get(v___y_1406_);
v_env_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_env_1409_);
lean_dec(v___x_1408_);
v___x_1410_ = 0;
lean_inc(v_constName_1396_);
v___x_1411_ = l_Lean_Environment_find_x3f(v_env_1409_, v_constName_1396_, v___x_1410_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1412_;
}
else
{
lean_object* v_val_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_constName_1396_);
v_val_1413_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1411_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_val_1413_);
lean_dec(v___x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 0);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_val_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec(v___y_1422_);
return v_res_1433_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1434_; double v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_float_of_nat(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_ref_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1493_; 
v_ref_1446_ = lean_ctor_get(v___y_1443_, 2);
v___x_1447_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1493_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1493_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v_traceState_1453_; lean_object* v_env_1454_; lean_object* v_nextMacroScope_1455_; lean_object* v_ngen_1456_; lean_object* v_auxDeclNGen_1457_; lean_object* v_cache_1458_; lean_object* v_recordedDeps_1459_; lean_object* v_messages_1460_; lean_object* v_infoState_1461_; lean_object* v_snapshotTasks_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1492_; 
v___x_1452_ = lean_st_ref_take(v___y_1444_);
v_traceState_1453_ = lean_ctor_get(v___x_1452_, 4);
v_env_1454_ = lean_ctor_get(v___x_1452_, 0);
v_nextMacroScope_1455_ = lean_ctor_get(v___x_1452_, 1);
v_ngen_1456_ = lean_ctor_get(v___x_1452_, 2);
v_auxDeclNGen_1457_ = lean_ctor_get(v___x_1452_, 3);
v_cache_1458_ = lean_ctor_get(v___x_1452_, 5);
v_recordedDeps_1459_ = lean_ctor_get(v___x_1452_, 6);
v_messages_1460_ = lean_ctor_get(v___x_1452_, 7);
v_infoState_1461_ = lean_ctor_get(v___x_1452_, 8);
v_snapshotTasks_1462_ = lean_ctor_get(v___x_1452_, 9);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1464_ = v___x_1452_;
v_isShared_1465_ = v_isSharedCheck_1492_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snapshotTasks_1462_);
lean_inc(v_infoState_1461_);
lean_inc(v_messages_1460_);
lean_inc(v_recordedDeps_1459_);
lean_inc(v_cache_1458_);
lean_inc(v_traceState_1453_);
lean_inc(v_auxDeclNGen_1457_);
lean_inc(v_ngen_1456_);
lean_inc(v_nextMacroScope_1455_);
lean_inc(v_env_1454_);
lean_dec(v___x_1452_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1492_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint64_t v_tid_1466_; lean_object* v_traces_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1491_; 
v_tid_1466_ = lean_ctor_get_uint64(v_traceState_1453_, sizeof(void*)*1);
v_traces_1467_ = lean_ctor_get(v_traceState_1453_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_traceState_1453_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1469_ = v_traceState_1453_;
v_isShared_1470_ = v_isSharedCheck_1491_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_traces_1467_);
lean_dec(v_traceState_1453_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1491_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; double v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1474_ = 0;
v___x_1475_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1476_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1476_, 0, v_cls_1439_);
lean_ctor_set(v___x_1476_, 1, v___x_1472_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
lean_ctor_set_float(v___x_1476_, sizeof(void*)*3, v___x_1473_);
lean_ctor_set_float(v___x_1476_, sizeof(void*)*3 + 8, v___x_1473_);
lean_ctor_set_uint8(v___x_1476_, sizeof(void*)*3 + 16, v___x_1474_);
v___x_1477_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1478_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v_a_1448_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
lean_inc(v_ref_1446_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_ref_1446_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_PersistentArray_push___redArg(v_traces_1467_, v___x_1479_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1480_);
v___x_1482_ = v___x_1469_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1480_);
lean_ctor_set_uint64(v_reuseFailAlloc_1490_, sizeof(void*)*1, v_tid_1466_);
v___x_1482_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1482_);
v___x_1484_ = v___x_1464_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_env_1454_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_nextMacroScope_1455_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_ngen_1456_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_auxDeclNGen_1457_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1489_, 5, v_cache_1458_);
lean_ctor_set(v_reuseFailAlloc_1489_, 6, v_recordedDeps_1459_);
lean_ctor_set(v_reuseFailAlloc_1489_, 7, v_messages_1460_);
lean_ctor_set(v_reuseFailAlloc_1489_, 8, v_infoState_1461_);
lean_ctor_set(v_reuseFailAlloc_1489_, 9, v_snapshotTasks_1462_);
v___x_1484_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_st_ref_put(v___y_1444_, v___x_1484_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1471_);
v___x_1487_ = v___x_1450_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1471_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1494_, v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1520_ = l_Lean_Name_append(v___x_1519_, v___x_1518_);
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___x_1794_; 
lean_inc_ref(v_e_1533_);
v___x_1794_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1533_, v_a_1541_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1823_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1823_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1823_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = l_Lean_Expr_cleanupAnnotations(v_a_1795_);
lean_dec(v_a_1795_);
v___x_1800_ = l_Lean_Expr_isApp(v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v___x_1799_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1799_);
v___x_1802_ = l_Lean_Expr_isApp(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1799_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
lean_object* v_arg_1803_; lean_object* v_arg_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_arg_1803_ = lean_ctor_get(v___x_1799_, 1);
lean_inc_ref(v_arg_1803_);
lean_dec_ref(v___x_1799_);
v_arg_1804_ = lean_ctor_get(v___x_1801_, 1);
lean_inc_ref(v_arg_1804_);
v___x_1805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1807_ = l_Lean_Expr_isConstOf(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1809_ = l_Lean_Expr_isConstOf(v___x_1805_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Lean_Expr_isApp(v___x_1805_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1805_);
lean_dec_ref(v___x_1805_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1813_ = l_Lean_Expr_isConstOf(v___x_1811_, v___x_1812_);
lean_dec_ref(v___x_1811_);
if (v___x_1813_ == 0)
{
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1533_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_e_1533_);
v___x_1815_ = lean_unsigned_to_nat(2u);
v___x_1816_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*1, v___x_1814_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*1 + 1, v___x_1814_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1816_);
v___x_1818_ = v___x_1797_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
lean_object* v___x_1820_; 
lean_del_object(v___x_1797_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1533_, v_arg_1804_, v_arg_1803_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1820_;
}
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v___x_1805_);
lean_del_object(v___x_1797_);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1533_, v_arg_1804_, v_arg_1803_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1821_;
}
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1805_);
lean_del_object(v___x_1797_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1533_, v_arg_1804_, v_arg_1803_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1822_;
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v_e_1533_);
v_a_1824_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1794_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1794_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
v___jp_1545_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
v___jp_1548_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
v___jp_1551_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
v___jp_1554_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = l_Lean_Expr_getAppNumArgs(v_e_1533_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v___x_1561_);
lean_dec(v___x_1562_);
v___x_1564_ = lean_nat_sub(v___x_1563_, v___x_1561_);
lean_dec(v___x_1563_);
v___x_1565_ = l_Lean_Expr_getRevArg_x21(v_e_1533_, v___x_1564_);
lean_dec_ref(v_e_1533_);
v___x_1566_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1565_, v___y_1560_, v___y_1558_, v___y_1559_, v___y_1557_, v___y_1556_, v___y_1555_);
return v___x_1566_;
}
v___jp_1567_:
{
uint8_t v___x_1579_; 
v___x_1579_ = l_Lean_Expr_isFVar(v_e_1533_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_e_1533_);
v___x_1580_ = lean_box(1);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; 
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc_ref(v_e_1533_);
v___x_1582_ = lean_infer_type(v_e_1533_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Meta_whnfD(v_a_1583_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_n(v_a_1585_, 2);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1587_ = l_Lean_MessageData_ofExpr(v_e_1533_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l_Lean_indentExpr(v_a_1585_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_Expr_getAppFn(v_a_1585_);
lean_dec(v_a_1585_);
if (lean_obj_tag(v___x_1593_) == 4)
{
lean_object* v_declName_1594_; lean_object* v___x_1595_; 
v_declName_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_declName_1594_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1595_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1594_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1628_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1628_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1628_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
if (lean_obj_tag(v_a_1596_) == 5)
{
lean_object* v_val_1600_; lean_object* v_ctors_1601_; uint8_t v_isRec_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_dec_ref_known(v___x_1592_, 2);
v_val_1600_ = lean_ctor_get(v_a_1596_, 0);
lean_inc_ref(v_val_1600_);
lean_dec_ref_known(v_a_1596_, 1);
v_ctors_1601_ = lean_ctor_get(v_val_1600_, 4);
lean_inc(v_ctors_1601_);
v_isRec_1602_ = lean_ctor_get_uint8(v_val_1600_, sizeof(void*)*6);
lean_dec_ref(v_val_1600_);
v___x_1603_ = l_List_lengthTR___redArg(v_ctors_1601_);
lean_dec(v_ctors_1601_);
v___x_1604_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*1, v_isRec_1602_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*1 + 1, v___y_1568_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1604_);
v___x_1606_ = v___x_1598_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
else
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1598_);
lean_dec(v_a_1596_);
v___x_1608_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1573_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; uint8_t v_verbose_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_verbose_1610_ = lean_ctor_get_uint8(v_a_1609_, 0);
lean_dec(v_a_1609_);
if (v_verbose_1610_ == 0)
{
lean_dec_ref_known(v___x_1592_, 2);
goto v___jp_1548_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_Sym_reportIssue(v___x_1592_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_dec_ref_known(v___x_1611_, 1);
goto v___jp_1548_;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref_known(v___x_1592_, 2);
v_a_1620_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1608_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1608_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref_known(v___x_1592_, 2);
v_a_1629_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1595_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1595_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1593_);
v___x_1637_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1573_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; uint8_t v_verbose_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v_verbose_1639_ = lean_ctor_get_uint8(v_a_1638_, 0);
lean_dec(v_a_1638_);
if (v_verbose_1639_ == 0)
{
lean_dec_ref_known(v___x_1592_, 2);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Sym_reportIssue(v___x_1592_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec_ref_known(v___x_1640_, 1);
goto v___jp_1551_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref_known(v___x_1592_, 2);
v_a_1649_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1637_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1637_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_e_1533_);
v_a_1657_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1584_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1584_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v_e_1533_);
v_a_1665_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1582_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1582_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
v___jp_1673_:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_isIte(v_e_1533_);
if (v___x_1684_ == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = l_Lean_Meta_Grind_isDIte(v_e_1533_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1533_, v___y_1674_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_inc_ref(v_e_1533_);
v___x_1689_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1533_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1749_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1749_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1749_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_unbox(v_a_1690_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v_env_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_st_ref_get(v___y_1683_);
v_env_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc_ref(v_env_1696_);
lean_dec(v___x_1695_);
v___x_1697_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1696_, v_e_1533_);
if (lean_obj_tag(v___x_1697_) == 1)
{
lean_object* v_val_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1704_; 
lean_dec_ref(v_e_1533_);
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1698_);
lean_dec(v_val_1698_);
v___x_1700_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
v___x_1701_ = lean_unbox(v_a_1690_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*1, v___x_1701_);
v___x_1702_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*1 + 1, v___x_1702_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1700_);
v___x_1704_ = v___x_1692_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1700_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v___x_1706_; 
lean_dec(v___x_1697_);
lean_del_object(v___x_1692_);
v___x_1706_ = l_Lean_Expr_getAppFn(v_e_1533_);
if (lean_obj_tag(v___x_1706_) == 4)
{
lean_object* v_declName_1707_; lean_object* v___x_1708_; 
v_declName_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_declName_1707_);
lean_dec_ref_known(v___x_1706_, 2);
v___x_1708_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1707_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
if (lean_obj_tag(v_a_1709_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1711_; 
v_val_1710_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_a_1709_, 1);
lean_inc_ref(v_e_1533_);
v___x_1711_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1533_, v___y_1674_, v___y_1678_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1726_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_unbox(v_a_1712_);
lean_dec(v_a_1712_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; 
lean_del_object(v___x_1714_);
lean_dec(v_val_1710_);
v___x_1717_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
v___y_1568_ = v___x_1717_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
goto v___jp_1567_;
}
else
{
lean_object* v_ctors_1718_; uint8_t v_isRec_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; lean_object* v___x_1724_; 
lean_dec_ref(v_e_1533_);
v_ctors_1718_ = lean_ctor_get(v_val_1710_, 4);
lean_inc(v_ctors_1718_);
v_isRec_1719_ = lean_ctor_get_uint8(v_val_1710_, sizeof(void*)*6);
lean_dec(v_val_1710_);
v___x_1720_ = l_List_lengthTR___redArg(v_ctors_1718_);
lean_dec(v_ctors_1718_);
v___x_1721_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1, v_isRec_1719_);
v___x_1722_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1 + 1, v___x_1722_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1721_);
v___x_1724_ = v___x_1714_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1721_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_val_1710_);
lean_dec(v_a_1690_);
lean_dec_ref(v_e_1533_);
v_a_1727_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1711_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1711_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
uint8_t v___x_1735_; 
lean_dec(v_a_1709_);
v___x_1735_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
v___y_1568_ = v___x_1735_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1690_);
lean_dec_ref(v_e_1533_);
v_a_1736_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1708_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1708_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
uint8_t v___x_1744_; 
lean_dec_ref(v___x_1706_);
v___x_1744_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
v___y_1568_ = v___x_1744_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec(v_a_1690_);
lean_dec_ref(v_e_1533_);
v___x_1745_ = lean_box(0);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1745_);
v___x_1747_ = v___x_1692_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_e_1533_);
v_a_1750_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1689_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1689_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_toCold_1758_; lean_object* v_options_1759_; uint8_t v_hasTrace_1760_; 
v_toCold_1758_ = lean_ctor_get(v___y_1682_, 0);
v_options_1759_ = lean_ctor_get(v_toCold_1758_, 2);
v_hasTrace_1760_ = lean_ctor_get_uint8(v_options_1759_, sizeof(void*)*1);
if (v_hasTrace_1760_ == 0)
{
lean_dec_ref(v_e_1533_);
goto v___jp_1545_;
}
else
{
lean_object* v_inheritedTraceOptions_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_inheritedTraceOptions_1761_ = lean_ctor_get(v_toCold_1758_, 11);
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1761_, v_options_1759_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v_e_1533_);
goto v___jp_1545_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_Grind_updateLastTag(v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec_ref_known(v___x_1765_, 1);
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1767_ = l_Lean_MessageData_ofExpr(v_e_1533_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1762_, v___x_1768_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref_known(v___x_1769_, 1);
goto v___jp_1545_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v_e_1533_);
v_a_1778_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1765_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1765_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v_e_1533_);
v_a_1786_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1686_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1686_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
v___y_1555_ = v___y_1683_;
v___y_1556_ = v___y_1682_;
v___y_1557_ = v___y_1681_;
v___y_1558_ = v___y_1678_;
v___y_1559_ = v___y_1680_;
v___y_1560_ = v___y_1674_;
goto v___jp_1554_;
}
}
else
{
v___y_1555_ = v___y_1683_;
v___y_1556_ = v___y_1682_;
v___y_1557_ = v___y_1681_;
v___y_1558_ = v___y_1678_;
v___y_1559_ = v___y_1680_;
v___y_1560_ = v___y_1674_;
goto v___jp_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec(v_a_1833_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1845_, lean_object* v_msg_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1845_, v_msg_1846_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1859_, v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v___y_1861_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1873_, lean_object* v_constName_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_constName_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1887_, v_constName_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1901_, lean_object* v_ref_1902_, lean_object* v_constName_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1902_, v_constName_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_ref_1917_, lean_object* v_constName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1916_, v_ref_1917_, v_constName_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v_ref_1917_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1931_, lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v_declHint_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1932_, v_msg_1933_, v_declHint_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_ref_1948_, lean_object* v_msg_1949_, lean_object* v_declHint_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1947_, v_ref_1948_, v_msg_1949_, v_declHint_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v_ref_1948_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1963_, lean_object* v_declHint_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1963_, v_declHint_1964_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1977_, lean_object* v_declHint_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1977_, v_declHint_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec(v___y_1979_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1991_, lean_object* v_ref_1992_, lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1992_, v_msg_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_ref_2007_, lean_object* v_msg_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2006_, v_ref_2007_, v_msg_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v_ref_2007_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2021_, lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2022_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_msg_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2035_, v_msg_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2049_, lean_object* v_x_2050_){
_start:
{
if (lean_obj_tag(v_x_2050_) == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_box(0);
return v___x_2051_;
}
else
{
lean_object* v_key_2052_; lean_object* v_value_2053_; lean_object* v_tail_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v_fst_2057_; lean_object* v_snd_2058_; uint8_t v___x_2059_; 
v_key_2052_ = lean_ctor_get(v_x_2050_, 0);
v_value_2053_ = lean_ctor_get(v_x_2050_, 1);
v_tail_2054_ = lean_ctor_get(v_x_2050_, 2);
v_fst_2055_ = lean_ctor_get(v_key_2052_, 0);
v_snd_2056_ = lean_ctor_get(v_key_2052_, 1);
v_fst_2057_ = lean_ctor_get(v_a_2049_, 0);
v_snd_2058_ = lean_ctor_get(v_a_2049_, 1);
v___x_2059_ = lean_expr_eqv(v_fst_2055_, v_fst_2057_);
if (v___x_2059_ == 0)
{
v_x_2050_ = v_tail_2054_;
goto _start;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_expr_eqv(v_snd_2056_, v_snd_2058_);
if (v___x_2061_ == 0)
{
v_x_2050_ = v_tail_2054_;
goto _start;
}
else
{
lean_object* v___x_2063_; 
lean_inc(v_value_2053_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_value_2053_);
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2064_, v_x_2065_);
lean_dec(v_x_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_buckets_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2072_; uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v___x_2077_; uint64_t v_fold_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_buckets_2069_ = lean_ctor_get(v_m_2067_, 1);
v_fst_2070_ = lean_ctor_get(v_a_2068_, 0);
v_snd_2071_ = lean_ctor_get(v_a_2068_, 1);
v___x_2072_ = lean_array_get_size(v_buckets_2069_);
v___x_2073_ = l_Lean_Expr_hash(v_fst_2070_);
v___x_2074_ = l_Lean_Expr_hash(v_snd_2071_);
v___x_2075_ = lean_uint64_mix_hash(v___x_2073_, v___x_2074_);
v___x_2076_ = 32ULL;
v___x_2077_ = lean_uint64_shift_right(v___x_2075_, v___x_2076_);
v_fold_2078_ = lean_uint64_xor(v___x_2075_, v___x_2077_);
v___x_2079_ = 16ULL;
v___x_2080_ = lean_uint64_shift_right(v_fold_2078_, v___x_2079_);
v___x_2081_ = lean_uint64_xor(v_fold_2078_, v___x_2080_);
v___x_2082_ = lean_uint64_to_usize(v___x_2081_);
v___x_2083_ = lean_usize_of_nat(v___x_2072_);
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_sub(v___x_2083_, v___x_2084_);
v___x_2086_ = lean_usize_land(v___x_2082_, v___x_2085_);
v___x_2087_ = lean_array_uget_borrowed(v_buckets_2069_, v___x_2086_);
v___x_2088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2068_, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2089_, v_a_2090_);
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_m_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2092_, uint8_t v___x_2093_, lean_object* v_fst_2094_, lean_object* v_snd_2095_, lean_object* v___x_2096_, lean_object* v_____r_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2109_ = lean_unsigned_to_nat(2u);
v___x_2110_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*1, v_a_2092_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*1 + 1, v___x_2093_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_fst_2094_);
lean_ctor_set(v___x_2112_, 1, v_snd_2095_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2096_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2111_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2117_ = _args[0];
lean_object* v___x_2118_ = _args[1];
lean_object* v_fst_2119_ = _args[2];
lean_object* v_snd_2120_ = _args[3];
lean_object* v___x_2121_ = _args[4];
lean_object* v_____r_2122_ = _args[5];
lean_object* v___y_2123_ = _args[6];
lean_object* v___y_2124_ = _args[7];
lean_object* v___y_2125_ = _args[8];
lean_object* v___y_2126_ = _args[9];
lean_object* v___y_2127_ = _args[10];
lean_object* v___y_2128_ = _args[11];
lean_object* v___y_2129_ = _args[12];
lean_object* v___y_2130_ = _args[13];
lean_object* v___y_2131_ = _args[14];
lean_object* v___y_2132_ = _args[15];
lean_object* v___y_2133_ = _args[16];
_start:
{
uint8_t v_a_34317__boxed_2134_; uint8_t v___x_34318__boxed_2135_; lean_object* v_res_2136_; 
v_a_34317__boxed_2134_ = lean_unbox(v_a_2117_);
v___x_34318__boxed_2135_ = lean_unbox(v___x_2118_);
v_res_2136_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34317__boxed_2134_, v___x_34318__boxed_2135_, v_fst_2119_, v_snd_2120_, v___x_2121_, v_____r_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v___y_2123_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2137_, lean_object* v_snd_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v_____r_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2153_ = l_Lean_Expr_appFn_x21(v_fst_2137_);
v___x_2154_ = l_Lean_Expr_appFn_x21(v_snd_2138_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2139_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2140_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2160_, lean_object* v_snd_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_____r_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2160_, v_snd_2161_, v___x_2162_, v___x_2163_, v_____r_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v_snd_2161_);
lean_dec(v_fst_2160_);
return v_res_2176_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___f_2178_; 
v___x_2177_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2178_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2178_, 0, v___x_2177_);
return v___f_2178_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2184_ = l_Lean_Name_append(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2203_, lean_object* v___y_2204_, lean_object* v_eq_2205_, lean_object* v_a_2206_, lean_object* v_b_2207_, lean_object* v_a_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___y_2221_; lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2363_; 
v_snd_2241_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_a_2208_, 0);
lean_dec(v_unused_2364_);
v___x_2243_ = v_a_2208_;
v_isShared_2244_ = v_isSharedCheck_2363_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_dec(v_a_2208_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2363_;
goto v_resetjp_2242_;
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2232_; 
v_a_2222_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2224_ = v___y_2221_;
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___y_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; 
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2226_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_a_2222_, 1);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_a_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v_a_2230_; 
lean_del_object(v___x_2224_);
v_a_2230_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_a_2222_, 1);
v_a_2208_ = v_a_2230_;
goto _start;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2233_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___y_2221_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___y_2221_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
v_resetjp_2242_:
{
lean_object* v_snd_2245_; lean_object* v_fst_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2362_; 
v_snd_2245_ = lean_ctor_get(v_snd_2241_, 1);
v_fst_2246_ = lean_ctor_get(v_snd_2241_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_snd_2241_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2248_ = v_snd_2241_;
v_isShared_2249_ = v_isSharedCheck_2362_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snd_2245_);
lean_inc(v_fst_2246_);
lean_dec(v_snd_2241_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2362_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2361_; 
v_fst_2250_ = lean_ctor_get(v_snd_2245_, 0);
v_snd_2251_ = lean_ctor_get(v_snd_2245_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_snd_2245_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2253_ = v_snd_2245_;
v_isShared_2254_ = v_isSharedCheck_2361_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2251_);
lean_inc(v_fst_2250_);
lean_dec(v_snd_2245_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2361_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
uint8_t v___y_2256_; uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Expr_isApp(v_fst_2250_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v___y_2256_ = v_a_2203_;
goto v___jp_2255_;
}
else
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Expr_isApp(v_snd_2251_);
if (v___x_2271_ == 0)
{
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v___y_2256_ = v___x_2271_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; uint8_t v___x_2276_; 
lean_del_object(v___x_2253_);
lean_del_object(v___x_2248_);
lean_del_object(v___x_2243_);
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_unsigned_to_nat(1u);
v___x_2274_ = lean_nat_sub(v_fst_2246_, v___x_2273_);
lean_dec(v_fst_2246_);
v___f_2275_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2204_);
lean_inc(v___x_2274_);
v___x_2276_ = l_List_elem___redArg(v___f_2275_, v___x_2274_, v___y_2204_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = l_Lean_Expr_appArg_x21(v_fst_2250_);
v___x_2278_ = l_Lean_Expr_appArg_x21(v_snd_2251_);
v___x_2279_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2277_, v___x_2278_, v___y_2209_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = lean_unbox(v_a_2280_);
if (v___x_2281_ == 0)
{
lean_object* v_toCold_2282_; lean_object* v_options_2283_; lean_object* v_inheritedTraceOptions_2284_; uint8_t v_hasTrace_2285_; 
v_toCold_2282_ = lean_ctor_get(v___y_2217_, 0);
v_options_2283_ = lean_ctor_get(v_toCold_2282_, 2);
v_inheritedTraceOptions_2284_ = lean_ctor_get(v_toCold_2282_, 11);
v_hasTrace_2285_ = lean_ctor_get_uint8(v_options_2283_, sizeof(void*)*1);
if (v_hasTrace_2285_ == 0)
{
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
goto v___jp_2286_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2290_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2291_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2284_, v_options_2283_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
goto v___jp_2286_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Meta_Grind_updateLastTag(v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; 
lean_dec_ref_known(v___x_2293_, 1);
v___x_2294_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2205_, v___y_2209_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2206_);
v___x_2297_ = l_Lean_MessageData_ofExpr(v_a_2206_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
lean_inc_ref(v_b_2207_);
v___x_2301_ = l_Lean_MessageData_ofExpr(v_b_2207_);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
lean_inc_ref(v_eq_2205_);
v___x_2305_ = l_Lean_MessageData_ofExpr(v_eq_2205_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = l_Lean_MessageData_ofExpr(v___x_2277_);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l_Lean_MessageData_ofExpr(v___x_2278_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Nat_reprFast(v_a_2295_);
v___x_2318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_ofFormat(v___x_2318_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2316_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2290_, v___x_2320_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___x_2324_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2323_, v___x_2271_, v_fst_2250_, v_snd_2251_, v___x_2274_, v_a_2322_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
v___y_2221_ = v___x_2324_;
goto v___jp_2220_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2280_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2325_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2321_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2321_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_a_2280_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2333_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2294_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2294_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2280_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2341_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2293_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2293_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
v___jp_2286_:
{
lean_object* v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___x_2289_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2288_, v___x_2271_, v_fst_2250_, v_snd_2251_, v___x_2274_, v___x_2287_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
v___y_2221_ = v___x_2289_;
goto v___jp_2220_;
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v_a_2280_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
v___x_2349_ = lean_box(0);
v___x_2350_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2250_, v_snd_2251_, v___x_2274_, v___x_2272_, v___x_2349_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
v___y_2221_ = v___x_2350_;
goto v___jp_2220_;
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2351_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2279_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2279_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2250_, v_snd_2251_, v___x_2274_, v___x_2272_, v___x_2359_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
v___y_2221_ = v___x_2360_;
goto v___jp_2220_;
}
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2257_ = lean_unsigned_to_nat(2u);
v___x_2258_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set_uint8(v___x_2258_, sizeof(void*)*1, v___y_2256_);
lean_ctor_set_uint8(v___x_2258_, sizeof(void*)*1 + 1, v___y_2256_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
if (v_isShared_2254_ == 0)
{
v___x_2261_ = v___x_2253_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_fst_2250_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_snd_2251_);
v___x_2261_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2261_);
v___x_2263_ = v___x_2248_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_fst_2246_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2265_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2263_);
lean_ctor_set(v___x_2243_, 0, v___x_2259_);
v___x_2265_ = v___x_2243_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
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
lean_object* v_a_2365_ = _args[0];
lean_object* v___y_2366_ = _args[1];
lean_object* v_eq_2367_ = _args[2];
lean_object* v_a_2368_ = _args[3];
lean_object* v_b_2369_ = _args[4];
lean_object* v_a_2370_ = _args[5];
lean_object* v___y_2371_ = _args[6];
lean_object* v___y_2372_ = _args[7];
lean_object* v___y_2373_ = _args[8];
lean_object* v___y_2374_ = _args[9];
lean_object* v___y_2375_ = _args[10];
lean_object* v___y_2376_ = _args[11];
lean_object* v___y_2377_ = _args[12];
lean_object* v___y_2378_ = _args[13];
lean_object* v___y_2379_ = _args[14];
lean_object* v___y_2380_ = _args[15];
lean_object* v___y_2381_ = _args[16];
_start:
{
uint8_t v_a_34491__boxed_2382_; lean_object* v_res_2383_; 
v_a_34491__boxed_2382_ = lean_unbox(v_a_2365_);
v_res_2383_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34491__boxed_2382_, v___y_2366_, v_eq_2367_, v_a_2368_, v_b_2369_, v_a_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2384_, lean_object* v_b_2385_, lean_object* v_eq_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2401_; 
lean_inc_ref(v_eq_2386_);
v___x_2401_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2386_, v_a_2387_, v_a_2391_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; uint8_t v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v___x_2403_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
lean_inc_ref(v_eq_2386_);
v___x_2404_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2386_, v_a_2387_, v_a_2391_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; uint8_t v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = lean_unbox(v_a_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___y_2409_; lean_object* v_toGoalState_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2454_; 
v___x_2407_ = lean_st_ref_get(v_a_2387_);
v_toGoalState_2442_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v___x_2407_, 1);
lean_dec(v_unused_2455_);
v___x_2444_ = v___x_2407_;
v_isShared_2445_ = v_isSharedCheck_2454_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_toGoalState_2442_);
lean_dec(v___x_2407_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2454_;
goto v_resetjp_2443_;
}
v___jp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2410_ = l_Lean_Expr_getAppNumArgs(v_a_2384_);
v___x_2411_ = lean_box(0);
lean_inc_ref(v_b_2385_);
lean_inc_ref(v_a_2384_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v_a_2384_);
lean_ctor_set(v___x_2412_, 1, v_b_2385_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2411_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_unbox(v_a_2405_);
v___x_2416_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___x_2415_, v___y_2409_, v_eq_2386_, v_a_2384_, v_b_2385_, v___x_2414_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2433_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2433_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2433_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_fst_2421_; 
v_fst_2421_ = lean_ctor_get(v_a_2417_, 0);
lean_inc(v_fst_2421_);
lean_dec(v_a_2417_);
if (lean_obj_tag(v_fst_2421_) == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2427_; 
v___x_2422_ = lean_unsigned_to_nat(2u);
v___x_2423_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
v___x_2424_ = lean_unbox(v_a_2405_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1, v___x_2424_);
v___x_2425_ = lean_unbox(v_a_2405_);
lean_dec(v_a_2405_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1 + 1, v___x_2425_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2423_);
v___x_2427_ = v___x_2419_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2423_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v_val_2429_; lean_object* v___x_2431_; 
lean_dec(v_a_2405_);
v_val_2429_ = lean_ctor_get(v_fst_2421_, 0);
lean_inc(v_val_2429_);
lean_dec_ref_known(v_fst_2421_, 1);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_val_2429_);
v___x_2431_ = v___x_2419_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_val_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_a_2405_);
v_a_2434_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2416_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2416_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
v_resetjp_2443_:
{
lean_object* v_split_2446_; lean_object* v_argPosMap_2447_; lean_object* v___x_2449_; 
v_split_2446_ = lean_ctor_get(v_toGoalState_2442_, 15);
lean_inc_ref(v_split_2446_);
lean_dec_ref(v_toGoalState_2442_);
v_argPosMap_2447_ = lean_ctor_get(v_split_2446_, 6);
lean_inc_ref(v_argPosMap_2447_);
lean_dec_ref(v_split_2446_);
lean_inc_ref(v_b_2385_);
lean_inc_ref(v_a_2384_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v_b_2385_);
lean_ctor_set(v___x_2444_, 0, v_a_2384_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2384_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_b_2385_);
v___x_2449_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2447_, v___x_2449_);
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_argPosMap_2447_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_box(0);
v___y_2409_ = v___x_2451_;
goto v___jp_2408_;
}
else
{
lean_object* v_val_2452_; 
v_val_2452_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2452_);
lean_dec_ref_known(v___x_2450_, 1);
v___y_2409_ = v_val_2452_;
goto v___jp_2408_;
}
}
}
}
else
{
lean_dec(v_a_2405_);
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
goto v___jp_2398_;
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
v_a_2456_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2404_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2404_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
goto v___jp_2398_;
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
v_a_2464_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2401_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2401_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
v___jp_2398_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2472_, lean_object* v_b_2473_, lean_object* v_eq_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2472_, v_b_2473_, v_eq_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec(v_a_2475_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2487_, lean_object* v___y_2488_, lean_object* v_eq_2489_, lean_object* v_a_2490_, lean_object* v_b_2491_, lean_object* v_inst_2492_, lean_object* v_a_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2487_, v___y_2488_, v_eq_2489_, v_a_2490_, v_b_2491_, v_a_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2506_ = _args[0];
lean_object* v___y_2507_ = _args[1];
lean_object* v_eq_2508_ = _args[2];
lean_object* v_a_2509_ = _args[3];
lean_object* v_b_2510_ = _args[4];
lean_object* v_inst_2511_ = _args[5];
lean_object* v_a_2512_ = _args[6];
lean_object* v___y_2513_ = _args[7];
lean_object* v___y_2514_ = _args[8];
lean_object* v___y_2515_ = _args[9];
lean_object* v___y_2516_ = _args[10];
lean_object* v___y_2517_ = _args[11];
lean_object* v___y_2518_ = _args[12];
lean_object* v___y_2519_ = _args[13];
lean_object* v___y_2520_ = _args[14];
lean_object* v___y_2521_ = _args[15];
lean_object* v___y_2522_ = _args[16];
lean_object* v___y_2523_ = _args[17];
_start:
{
uint8_t v_a_34972__boxed_2524_; lean_object* v_res_2525_; 
v_a_34972__boxed_2524_ = lean_unbox(v_a_2506_);
v_res_2525_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34972__boxed_2524_, v___y_2507_, v_eq_2508_, v_a_2509_, v_b_2510_, v_inst_2511_, v_a_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2526_, lean_object* v_m_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2527_, v_a_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2530_, lean_object* v_m_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2530_, v_m_2531_, v_a_2532_);
lean_dec_ref(v_a_2532_);
lean_dec_ref(v_m_2531_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2534_, lean_object* v_a_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2535_, v_x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2538_, lean_object* v_a_2539_, lean_object* v_x_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2538_, v_a_2539_, v_x_2540_);
lean_dec(v_x_2540_);
lean_dec_ref(v_a_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v___x_2556_; 
lean_inc_ref(v_imp_2542_);
v___x_2556_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; uint8_t v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = lean_unbox(v_a_2557_);
lean_dec(v_a_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2573_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2573_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2573_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = lean_box(1);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2569_);
v___x_2571_ = v___x_2562_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2559_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2559_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_binderType_2582_; lean_object* v_body_2583_; lean_object* v___x_2584_; 
v_binderType_2582_ = lean_ctor_get(v_imp_2542_, 1);
lean_inc_ref_n(v_binderType_2582_, 2);
v_body_2583_ = lean_ctor_get(v_imp_2542_, 2);
lean_inc_ref(v_body_2583_);
lean_dec_ref(v_imp_2542_);
v___x_2584_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2582_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; uint8_t v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = lean_unbox(v_a_2585_);
lean_dec(v_a_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2582_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2624_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2624_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2624_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_unbox(v_a_2588_);
if (v___x_2600_ == 0)
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Lean_Expr_hasLooseBVars(v_body_2583_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_inc_ref(v_body_2583_);
v___x_2602_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2583_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; uint8_t v___x_2604_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v___x_2604_ = lean_unbox(v_a_2603_);
lean_dec(v_a_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2583_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; uint8_t v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
if (v___x_2607_ == 0)
{
goto v___jp_2592_;
}
else
{
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
goto v___jp_2550_;
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
v_a_2608_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2605_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2605_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_dec_ref(v_body_2583_);
goto v___jp_2550_;
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_dec_ref(v_body_2583_);
v_a_2616_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2602_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2602_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_dec_ref(v_body_2583_);
goto v___jp_2592_;
}
}
else
{
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_dec_ref(v_body_2583_);
goto v___jp_2553_;
}
v___jp_2592_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2598_; 
v___x_2593_ = lean_unsigned_to_nat(2u);
v___x_2594_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
v___x_2595_ = lean_unbox(v_a_2588_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2595_);
v___x_2596_ = lean_unbox(v_a_2588_);
lean_dec(v_a_2588_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1 + 1, v___x_2596_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2594_);
v___x_2598_ = v___x_2590_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2594_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_body_2583_);
v_a_2625_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2587_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2587_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_dec_ref(v_body_2583_);
lean_dec_ref(v_binderType_2582_);
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v_body_2583_);
lean_dec_ref(v_binderType_2582_);
v_a_2633_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2584_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2584_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v_imp_2542_);
v_a_2641_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2556_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2556_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
v___jp_2550_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
v___jp_2553_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2658_, lean_object* v_h_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2658_, v_a_2660_, v_a_2664_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2672_, lean_object* v_h_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2672_, v_h_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec(v_a_2674_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
switch(lean_obj_tag(v_s_2686_))
{
case 0:
{
lean_object* v_e_2698_; lean_object* v___x_2699_; 
v_e_2698_ = lean_ctor_get(v_s_2686_, 0);
lean_inc_ref(v_e_2698_);
lean_dec_ref_known(v_s_2686_, 2);
v___x_2699_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2698_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2699_;
}
case 1:
{
lean_object* v_e_2700_; lean_object* v___x_2701_; 
v_e_2700_ = lean_ctor_get(v_s_2686_, 0);
lean_inc_ref(v_e_2700_);
lean_dec_ref_known(v_s_2686_, 2);
v___x_2701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2700_, v_a_2687_, v_a_2691_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2701_;
}
default: 
{
lean_object* v_a_2702_; lean_object* v_b_2703_; lean_object* v_eq_2704_; lean_object* v___x_2705_; 
v_a_2702_ = lean_ctor_get(v_s_2686_, 0);
lean_inc_ref(v_a_2702_);
v_b_2703_ = lean_ctor_get(v_s_2686_, 1);
lean_inc_ref(v_b_2703_);
v_eq_2704_ = lean_ctor_get(v_s_2686_, 3);
lean_inc_ref(v_eq_2704_);
lean_dec_ref_known(v_s_2686_, 5);
v___x_2705_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2702_, v_b_2703_, v_eq_2704_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec(v_a_2707_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_obj_tag_nat(v_x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2721_);
lean_dec(v_x_2721_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2723_, lean_object* v_k_2724_){
_start:
{
if (lean_obj_tag(v_t_2723_) == 0)
{
return v_k_2724_;
}
else
{
lean_object* v_c_2725_; lean_object* v_numCases_2726_; uint8_t v_isRec_2727_; uint8_t v_tryPostpone_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_c_2725_ = lean_ctor_get(v_t_2723_, 0);
lean_inc_ref(v_c_2725_);
v_numCases_2726_ = lean_ctor_get(v_t_2723_, 1);
lean_inc(v_numCases_2726_);
v_isRec_2727_ = lean_ctor_get_uint8(v_t_2723_, sizeof(void*)*2);
v_tryPostpone_2728_ = lean_ctor_get_uint8(v_t_2723_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2723_, 2);
v___x_2729_ = lean_box(v_isRec_2727_);
v___x_2730_ = lean_box(v_tryPostpone_2728_);
v___x_2731_ = lean_apply_4(v_k_2724_, v_c_2725_, v_numCases_2726_, v___x_2729_, v___x_2730_);
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2732_, lean_object* v_ctorIdx_2733_, lean_object* v_t_2734_, lean_object* v_h_2735_, lean_object* v_k_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2734_, v_k_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2738_, lean_object* v_ctorIdx_2739_, lean_object* v_t_2740_, lean_object* v_h_2741_, lean_object* v_k_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2738_, v_ctorIdx_2739_, v_t_2740_, v_h_2741_, v_k_2742_);
lean_dec(v_ctorIdx_2739_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2744_, lean_object* v_none_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2744_, v_none_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2747_, lean_object* v_t_2748_, lean_object* v_h_2749_, lean_object* v_none_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2748_, v_none_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2752_, lean_object* v_some_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2752_, v_some_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2755_, lean_object* v_t_2756_, lean_object* v_h_2757_, lean_object* v_some_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2756_, v_some_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2760_, lean_object* v_as_2761_, size_t v_i_2762_, size_t v_stop_2763_){
_start:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_usize_dec_eq(v_i_2762_, v_stop_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = lean_array_uget_borrowed(v_as_2761_, v_i_2762_);
v___x_2766_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2765_, v_a_2760_);
if (v___x_2766_ == 0)
{
size_t v___x_2767_; size_t v___x_2768_; 
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_add(v_i_2762_, v___x_2767_);
v_i_2762_ = v___x_2768_;
goto _start;
}
else
{
return v___x_2766_;
}
}
else
{
uint8_t v___x_2770_; 
v___x_2770_ = 0;
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2771_, lean_object* v_as_2772_, lean_object* v_i_2773_, lean_object* v_stop_2774_){
_start:
{
uint64_t v_a_2507__boxed_2775_; size_t v_i_boxed_2776_; size_t v_stop_boxed_2777_; uint8_t v_res_2778_; lean_object* v_r_2779_; 
v_a_2507__boxed_2775_ = lean_unbox_uint64(v_a_2771_);
lean_dec_ref(v_a_2771_);
v_i_boxed_2776_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_stop_boxed_2777_ = lean_unbox_usize(v_stop_2774_);
lean_dec(v_stop_2774_);
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2775_, v_as_2772_, v_i_boxed_2776_, v_stop_boxed_2777_);
lean_dec_ref(v_as_2772_);
v_r_2779_ = lean_box(v_res_2778_);
return v_r_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2782_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2835_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2835_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2835_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
if (lean_obj_tag(v_a_2792_) == 1)
{
lean_object* v_val_2796_; lean_object* v___x_2797_; 
lean_del_object(v___x_2794_);
v_val_2796_ = lean_ctor_get(v_a_2792_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v_a_2792_, 1);
v___x_2797_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2821_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2821_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2821_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = lean_array_get_size(v_val_2796_);
v___x_2804_ = lean_nat_dec_lt(v___x_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_dec(v_a_2798_);
lean_dec(v_val_2796_);
v___x_2805_ = lean_box(v___x_2804_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2805_);
v___x_2807_ = v___x_2800_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
else
{
if (v___x_2804_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
lean_dec(v_a_2798_);
lean_dec(v_val_2796_);
v___x_2809_ = lean_box(v___x_2804_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2809_);
v___x_2811_ = v___x_2800_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
size_t v___x_2813_; size_t v___x_2814_; uint64_t v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2813_ = ((size_t)0ULL);
v___x_2814_ = lean_usize_of_nat(v___x_2803_);
v___x_2815_ = lean_unbox_uint64(v_a_2798_);
lean_dec(v_a_2798_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2815_, v_val_2796_, v___x_2813_, v___x_2814_);
lean_dec(v_val_2796_);
v___x_2817_ = lean_box(v___x_2816_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2817_);
v___x_2819_ = v___x_2800_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_val_2796_);
v_a_2822_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2797_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2797_);
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
uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
lean_dec(v_a_2792_);
v___x_2830_ = 1;
v___x_2831_ = lean_box(v___x_2830_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2831_);
v___x_2833_ = v___x_2794_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
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
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_a_2836_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2791_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2791_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_c_2844_);
return v_res_2855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2858_ = l_Lean_stringToMessageData(v___x_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2859_, lean_object* v_c_x3f_2860_, lean_object* v_cs_x27_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
if (lean_obj_tag(v_cs_2859_) == 0)
{
lean_object* v___x_2873_; lean_object* v_toGoalState_2874_; lean_object* v_split_2875_; lean_object* v_mvarId_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2992_; 
v___x_2873_ = lean_st_ref_take(v_a_2862_);
v_toGoalState_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc_ref(v_toGoalState_2874_);
v_split_2875_ = lean_ctor_get(v_toGoalState_2874_, 15);
lean_inc_ref(v_split_2875_);
v_mvarId_2876_ = lean_ctor_get(v___x_2873_, 1);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2993_);
v___x_2878_ = v___x_2873_;
v_isShared_2879_ = v_isSharedCheck_2992_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_mvarId_2876_);
lean_dec(v___x_2873_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2992_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_nextDeclIdx_2880_; lean_object* v_enodeMap_2881_; lean_object* v_exprs_2882_; lean_object* v_parents_2883_; lean_object* v_congrTable_2884_; lean_object* v_appMap_2885_; lean_object* v_indicesFound_2886_; lean_object* v_toProcess_2887_; lean_object* v_internalizing_2888_; uint8_t v_inconsistent_2889_; lean_object* v_nextIdx_2890_; lean_object* v_newRawFacts_2891_; lean_object* v_facts_2892_; lean_object* v_extThms_2893_; lean_object* v_ematch_2894_; lean_object* v_inj_2895_; lean_object* v_clean_2896_; lean_object* v_sstates_2897_; lean_object* v_goalStack_2898_; uint64_t v_introBase_2899_; lean_object* v_numIntros_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2990_; 
v_nextDeclIdx_2880_ = lean_ctor_get(v_toGoalState_2874_, 0);
v_enodeMap_2881_ = lean_ctor_get(v_toGoalState_2874_, 1);
v_exprs_2882_ = lean_ctor_get(v_toGoalState_2874_, 2);
v_parents_2883_ = lean_ctor_get(v_toGoalState_2874_, 3);
v_congrTable_2884_ = lean_ctor_get(v_toGoalState_2874_, 4);
v_appMap_2885_ = lean_ctor_get(v_toGoalState_2874_, 5);
v_indicesFound_2886_ = lean_ctor_get(v_toGoalState_2874_, 6);
v_toProcess_2887_ = lean_ctor_get(v_toGoalState_2874_, 7);
v_internalizing_2888_ = lean_ctor_get(v_toGoalState_2874_, 8);
v_inconsistent_2889_ = lean_ctor_get_uint8(v_toGoalState_2874_, sizeof(void*)*20 + 8);
v_nextIdx_2890_ = lean_ctor_get(v_toGoalState_2874_, 9);
v_newRawFacts_2891_ = lean_ctor_get(v_toGoalState_2874_, 10);
v_facts_2892_ = lean_ctor_get(v_toGoalState_2874_, 11);
v_extThms_2893_ = lean_ctor_get(v_toGoalState_2874_, 12);
v_ematch_2894_ = lean_ctor_get(v_toGoalState_2874_, 13);
v_inj_2895_ = lean_ctor_get(v_toGoalState_2874_, 14);
v_clean_2896_ = lean_ctor_get(v_toGoalState_2874_, 16);
v_sstates_2897_ = lean_ctor_get(v_toGoalState_2874_, 17);
v_goalStack_2898_ = lean_ctor_get(v_toGoalState_2874_, 18);
v_introBase_2899_ = lean_ctor_get_uint64(v_toGoalState_2874_, sizeof(void*)*20);
v_numIntros_2900_ = lean_ctor_get(v_toGoalState_2874_, 19);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_toGoalState_2874_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v_toGoalState_2874_, 15);
lean_dec(v_unused_2991_);
v___x_2902_ = v_toGoalState_2874_;
v_isShared_2903_ = v_isSharedCheck_2990_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_numIntros_2900_);
lean_inc(v_goalStack_2898_);
lean_inc(v_sstates_2897_);
lean_inc(v_clean_2896_);
lean_inc(v_inj_2895_);
lean_inc(v_ematch_2894_);
lean_inc(v_extThms_2893_);
lean_inc(v_facts_2892_);
lean_inc(v_newRawFacts_2891_);
lean_inc(v_nextIdx_2890_);
lean_inc(v_internalizing_2888_);
lean_inc(v_toProcess_2887_);
lean_inc(v_indicesFound_2886_);
lean_inc(v_appMap_2885_);
lean_inc(v_congrTable_2884_);
lean_inc(v_parents_2883_);
lean_inc(v_exprs_2882_);
lean_inc(v_enodeMap_2881_);
lean_inc(v_nextDeclIdx_2880_);
lean_dec(v_toGoalState_2874_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2990_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v_num_2904_; lean_object* v_added_2905_; lean_object* v_resolved_2906_; lean_object* v_trace_2907_; lean_object* v_lookaheads_2908_; lean_object* v_argPosMap_2909_; lean_object* v_argsAt_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2988_; 
v_num_2904_ = lean_ctor_get(v_split_2875_, 0);
v_added_2905_ = lean_ctor_get(v_split_2875_, 2);
v_resolved_2906_ = lean_ctor_get(v_split_2875_, 3);
v_trace_2907_ = lean_ctor_get(v_split_2875_, 4);
v_lookaheads_2908_ = lean_ctor_get(v_split_2875_, 5);
v_argPosMap_2909_ = lean_ctor_get(v_split_2875_, 6);
v_argsAt_2910_ = lean_ctor_get(v_split_2875_, 7);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_split_2875_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v_split_2875_, 1);
lean_dec(v_unused_2989_);
v___x_2912_ = v_split_2875_;
v_isShared_2913_ = v_isSharedCheck_2988_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_argsAt_2910_);
lean_inc(v_argPosMap_2909_);
lean_inc(v_lookaheads_2908_);
lean_inc(v_trace_2907_);
lean_inc(v_resolved_2906_);
lean_inc(v_added_2905_);
lean_inc(v_num_2904_);
lean_dec(v_split_2875_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2988_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = l_List_reverse___redArg(v_cs_x27_2861_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v___x_2914_);
v___x_2916_ = v___x_2912_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_num_2904_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_added_2905_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_resolved_2906_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_trace_2907_);
lean_ctor_set(v_reuseFailAlloc_2987_, 5, v_lookaheads_2908_);
lean_ctor_set(v_reuseFailAlloc_2987_, 6, v_argPosMap_2909_);
lean_ctor_set(v_reuseFailAlloc_2987_, 7, v_argsAt_2910_);
v___x_2916_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 15, v___x_2916_);
v___x_2918_ = v___x_2902_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_nextDeclIdx_2880_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_enodeMap_2881_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_exprs_2882_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_parents_2883_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_congrTable_2884_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v_appMap_2885_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_indicesFound_2886_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_toProcess_2887_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_internalizing_2888_);
lean_ctor_set(v_reuseFailAlloc_2986_, 9, v_nextIdx_2890_);
lean_ctor_set(v_reuseFailAlloc_2986_, 10, v_newRawFacts_2891_);
lean_ctor_set(v_reuseFailAlloc_2986_, 11, v_facts_2892_);
lean_ctor_set(v_reuseFailAlloc_2986_, 12, v_extThms_2893_);
lean_ctor_set(v_reuseFailAlloc_2986_, 13, v_ematch_2894_);
lean_ctor_set(v_reuseFailAlloc_2986_, 14, v_inj_2895_);
lean_ctor_set(v_reuseFailAlloc_2986_, 15, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2986_, 16, v_clean_2896_);
lean_ctor_set(v_reuseFailAlloc_2986_, 17, v_sstates_2897_);
lean_ctor_set(v_reuseFailAlloc_2986_, 18, v_goalStack_2898_);
lean_ctor_set(v_reuseFailAlloc_2986_, 19, v_numIntros_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2986_, sizeof(void*)*20 + 8, v_inconsistent_2889_);
lean_ctor_set_uint64(v_reuseFailAlloc_2986_, sizeof(void*)*20, v_introBase_2899_);
v___x_2918_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2918_);
v___x_2920_ = v___x_2878_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_mvarId_2876_);
v___x_2920_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_st_ref_put(v_a_2862_, v___x_2920_);
if (lean_obj_tag(v_c_x3f_2860_) == 1)
{
lean_object* v___x_2922_; lean_object* v_toGoalState_2923_; lean_object* v_ematch_2924_; lean_object* v_mvarId_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2982_; 
v___x_2922_ = lean_st_ref_take(v_a_2862_);
v_toGoalState_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_ref(v_toGoalState_2923_);
v_ematch_2924_ = lean_ctor_get(v_toGoalState_2923_, 13);
lean_inc_ref(v_ematch_2924_);
v_mvarId_2925_ = lean_ctor_get(v___x_2922_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2983_);
v___x_2927_ = v___x_2922_;
v_isShared_2928_ = v_isSharedCheck_2982_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_mvarId_2925_);
lean_dec(v___x_2922_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2982_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v_nextDeclIdx_2929_; lean_object* v_enodeMap_2930_; lean_object* v_exprs_2931_; lean_object* v_parents_2932_; lean_object* v_congrTable_2933_; lean_object* v_appMap_2934_; lean_object* v_indicesFound_2935_; lean_object* v_toProcess_2936_; lean_object* v_internalizing_2937_; uint8_t v_inconsistent_2938_; lean_object* v_nextIdx_2939_; lean_object* v_newRawFacts_2940_; lean_object* v_facts_2941_; lean_object* v_extThms_2942_; lean_object* v_inj_2943_; lean_object* v_split_2944_; lean_object* v_clean_2945_; lean_object* v_sstates_2946_; lean_object* v_goalStack_2947_; uint64_t v_introBase_2948_; lean_object* v_numIntros_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2980_; 
v_nextDeclIdx_2929_ = lean_ctor_get(v_toGoalState_2923_, 0);
v_enodeMap_2930_ = lean_ctor_get(v_toGoalState_2923_, 1);
v_exprs_2931_ = lean_ctor_get(v_toGoalState_2923_, 2);
v_parents_2932_ = lean_ctor_get(v_toGoalState_2923_, 3);
v_congrTable_2933_ = lean_ctor_get(v_toGoalState_2923_, 4);
v_appMap_2934_ = lean_ctor_get(v_toGoalState_2923_, 5);
v_indicesFound_2935_ = lean_ctor_get(v_toGoalState_2923_, 6);
v_toProcess_2936_ = lean_ctor_get(v_toGoalState_2923_, 7);
v_internalizing_2937_ = lean_ctor_get(v_toGoalState_2923_, 8);
v_inconsistent_2938_ = lean_ctor_get_uint8(v_toGoalState_2923_, sizeof(void*)*20 + 8);
v_nextIdx_2939_ = lean_ctor_get(v_toGoalState_2923_, 9);
v_newRawFacts_2940_ = lean_ctor_get(v_toGoalState_2923_, 10);
v_facts_2941_ = lean_ctor_get(v_toGoalState_2923_, 11);
v_extThms_2942_ = lean_ctor_get(v_toGoalState_2923_, 12);
v_inj_2943_ = lean_ctor_get(v_toGoalState_2923_, 14);
v_split_2944_ = lean_ctor_get(v_toGoalState_2923_, 15);
v_clean_2945_ = lean_ctor_get(v_toGoalState_2923_, 16);
v_sstates_2946_ = lean_ctor_get(v_toGoalState_2923_, 17);
v_goalStack_2947_ = lean_ctor_get(v_toGoalState_2923_, 18);
v_introBase_2948_ = lean_ctor_get_uint64(v_toGoalState_2923_, sizeof(void*)*20);
v_numIntros_2949_ = lean_ctor_get(v_toGoalState_2923_, 19);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_toGoalState_2923_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v_toGoalState_2923_, 13);
lean_dec(v_unused_2981_);
v___x_2951_ = v_toGoalState_2923_;
v_isShared_2952_ = v_isSharedCheck_2980_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_numIntros_2949_);
lean_inc(v_goalStack_2947_);
lean_inc(v_sstates_2946_);
lean_inc(v_clean_2945_);
lean_inc(v_split_2944_);
lean_inc(v_inj_2943_);
lean_inc(v_extThms_2942_);
lean_inc(v_facts_2941_);
lean_inc(v_newRawFacts_2940_);
lean_inc(v_nextIdx_2939_);
lean_inc(v_internalizing_2937_);
lean_inc(v_toProcess_2936_);
lean_inc(v_indicesFound_2935_);
lean_inc(v_appMap_2934_);
lean_inc(v_congrTable_2933_);
lean_inc(v_parents_2932_);
lean_inc(v_exprs_2931_);
lean_inc(v_enodeMap_2930_);
lean_inc(v_nextDeclIdx_2929_);
lean_dec(v_toGoalState_2923_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2980_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_thmMap_2953_; lean_object* v_gmt_2954_; lean_object* v_thms_2955_; lean_object* v_newThms_2956_; lean_object* v_numInstances_2957_; lean_object* v_numDelayedInstances_2958_; lean_object* v_preInstances_2959_; lean_object* v_nextThmIdx_2960_; lean_object* v_matchEqNames_2961_; lean_object* v_delayedThmInsts_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2978_; 
v_thmMap_2953_ = lean_ctor_get(v_ematch_2924_, 0);
v_gmt_2954_ = lean_ctor_get(v_ematch_2924_, 1);
v_thms_2955_ = lean_ctor_get(v_ematch_2924_, 2);
v_newThms_2956_ = lean_ctor_get(v_ematch_2924_, 3);
v_numInstances_2957_ = lean_ctor_get(v_ematch_2924_, 4);
v_numDelayedInstances_2958_ = lean_ctor_get(v_ematch_2924_, 5);
v_preInstances_2959_ = lean_ctor_get(v_ematch_2924_, 7);
v_nextThmIdx_2960_ = lean_ctor_get(v_ematch_2924_, 8);
v_matchEqNames_2961_ = lean_ctor_get(v_ematch_2924_, 9);
v_delayedThmInsts_2962_ = lean_ctor_get(v_ematch_2924_, 10);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_ematch_2924_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_ematch_2924_, 6);
lean_dec(v_unused_2979_);
v___x_2964_ = v_ematch_2924_;
v_isShared_2965_ = v_isSharedCheck_2978_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_delayedThmInsts_2962_);
lean_inc(v_matchEqNames_2961_);
lean_inc(v_nextThmIdx_2960_);
lean_inc(v_preInstances_2959_);
lean_inc(v_numDelayedInstances_2958_);
lean_inc(v_numInstances_2957_);
lean_inc(v_newThms_2956_);
lean_inc(v_thms_2955_);
lean_inc(v_gmt_2954_);
lean_inc(v_thmMap_2953_);
lean_dec(v_ematch_2924_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2978_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2966_ = lean_unsigned_to_nat(0u);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 6, v___x_2966_);
v___x_2968_ = v___x_2964_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_thmMap_2953_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_gmt_2954_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_thms_2955_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_newThms_2956_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v_numInstances_2957_);
lean_ctor_set(v_reuseFailAlloc_2977_, 5, v_numDelayedInstances_2958_);
lean_ctor_set(v_reuseFailAlloc_2977_, 6, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2977_, 7, v_preInstances_2959_);
lean_ctor_set(v_reuseFailAlloc_2977_, 8, v_nextThmIdx_2960_);
lean_ctor_set(v_reuseFailAlloc_2977_, 9, v_matchEqNames_2961_);
lean_ctor_set(v_reuseFailAlloc_2977_, 10, v_delayedThmInsts_2962_);
v___x_2968_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 13, v___x_2968_);
v___x_2970_ = v___x_2951_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_nextDeclIdx_2929_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_enodeMap_2930_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_exprs_2931_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_parents_2932_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_congrTable_2933_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v_appMap_2934_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v_indicesFound_2935_);
lean_ctor_set(v_reuseFailAlloc_2976_, 7, v_toProcess_2936_);
lean_ctor_set(v_reuseFailAlloc_2976_, 8, v_internalizing_2937_);
lean_ctor_set(v_reuseFailAlloc_2976_, 9, v_nextIdx_2939_);
lean_ctor_set(v_reuseFailAlloc_2976_, 10, v_newRawFacts_2940_);
lean_ctor_set(v_reuseFailAlloc_2976_, 11, v_facts_2941_);
lean_ctor_set(v_reuseFailAlloc_2976_, 12, v_extThms_2942_);
lean_ctor_set(v_reuseFailAlloc_2976_, 13, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2976_, 14, v_inj_2943_);
lean_ctor_set(v_reuseFailAlloc_2976_, 15, v_split_2944_);
lean_ctor_set(v_reuseFailAlloc_2976_, 16, v_clean_2945_);
lean_ctor_set(v_reuseFailAlloc_2976_, 17, v_sstates_2946_);
lean_ctor_set(v_reuseFailAlloc_2976_, 18, v_goalStack_2947_);
lean_ctor_set(v_reuseFailAlloc_2976_, 19, v_numIntros_2949_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*20 + 8, v_inconsistent_2938_);
lean_ctor_set_uint64(v_reuseFailAlloc_2976_, sizeof(void*)*20, v_introBase_2948_);
v___x_2970_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2970_);
v___x_2972_ = v___x_2927_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_mvarId_2925_);
v___x_2972_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_st_ref_put(v_a_2862_, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_c_x3f_2860_);
return v___x_2974_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_c_x3f_2860_);
return v___x_2984_;
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
lean_object* v_head_2994_; lean_object* v_tail_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3215_; 
v_head_2994_ = lean_ctor_get(v_cs_2859_, 0);
v_tail_2995_ = lean_ctor_get(v_cs_2859_, 1);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_cs_2859_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_2997_ = v_cs_2859_;
v_isShared_2998_ = v_isSharedCheck_3215_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_tail_2995_);
lean_inc(v_head_2994_);
lean_dec(v_cs_2859_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3215_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3015_; uint8_t v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3033_; uint8_t v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3071_; uint8_t v___y_3072_; lean_object* v___y_3073_; uint8_t v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3089_; uint8_t v___y_3090_; lean_object* v___y_3091_; uint8_t v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; uint8_t v___y_3104_; lean_object* v___x_3107_; 
v___x_3107_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2994_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; uint8_t v___x_3109_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = lean_unbox(v_a_3108_);
lean_dec(v_a_3108_);
if (v___x_3109_ == 0)
{
lean_del_object(v___x_2997_);
lean_dec(v_head_2994_);
v_cs_2859_ = v_tail_2995_;
goto _start;
}
else
{
lean_object* v_toCold_3111_; lean_object* v_options_3112_; lean_object* v_inheritedTraceOptions_3113_; uint8_t v_hasTrace_3114_; uint8_t v___x_3115_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3119_; uint8_t v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; 
v_toCold_3111_ = lean_ctor_get(v_a_2870_, 0);
v_options_3112_ = lean_ctor_get(v_toCold_3111_, 2);
v_inheritedTraceOptions_3113_ = lean_ctor_get(v_toCold_3111_, 11);
v_hasTrace_3114_ = lean_ctor_get_uint8(v_options_3112_, sizeof(void*)*1);
v___x_3115_ = 0;
if (v_hasTrace_3114_ == 0)
{
v___y_3141_ = v_a_2862_;
v___y_3142_ = v_a_2863_;
v___y_3143_ = v_a_2864_;
v___y_3144_ = v_a_2865_;
v___y_3145_ = v_a_2866_;
v___y_3146_ = v_a_2867_;
v___y_3147_ = v_a_2868_;
v___y_3148_ = v_a_2869_;
v___y_3149_ = v_a_2870_;
v___y_3150_ = v_a_2871_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3113_, v_options_3112_, v___x_3183_);
if (v___x_3184_ == 0)
{
v___y_3141_ = v_a_2862_;
v___y_3142_ = v_a_2863_;
v___y_3143_ = v_a_2864_;
v___y_3144_ = v_a_2865_;
v___y_3145_ = v_a_2866_;
v___y_3146_ = v_a_2867_;
v___y_3147_ = v_a_2868_;
v___y_3148_ = v_a_2869_;
v___y_3149_ = v_a_2870_;
v___y_3150_ = v_a_2871_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_Meta_Grind_updateLastTag(v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_dec_ref_known(v___x_3185_, 1);
v___x_3186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3187_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2994_);
v___x_3188_ = l_Lean_MessageData_ofExpr(v___x_3187_);
v___x_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3186_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3182_, v___x_3189_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_dec_ref_known(v___x_3190_, 1);
v___y_3141_ = v_a_2862_;
v___y_3142_ = v_a_2863_;
v___y_3143_ = v_a_2864_;
v___y_3144_ = v_a_2865_;
v___y_3145_ = v_a_2866_;
v___y_3146_ = v_a_2867_;
v___y_3147_ = v_a_2868_;
v___y_3148_ = v_a_2869_;
v___y_3149_ = v_a_2870_;
v___y_3150_ = v_a_2871_;
goto v___jp_3140_;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3199_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3185_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3185_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
v___jp_3116_:
{
if (lean_obj_tag(v_c_x3f_2860_) == 0)
{
lean_object* v___x_3131_; 
lean_del_object(v___x_2997_);
v___x_3131_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3131_, 0, v_head_2994_);
lean_ctor_set(v___x_3131_, 1, v___y_3126_);
lean_ctor_set_uint8(v___x_3131_, sizeof(void*)*2, v___y_3118_);
lean_ctor_set_uint8(v___x_3131_, sizeof(void*)*2 + 1, v___y_3120_);
v_cs_2859_ = v_tail_2995_;
v_c_x3f_2860_ = v___x_3131_;
v_a_2862_ = v___y_3123_;
v_a_2863_ = v___y_3128_;
v_a_2864_ = v___y_3124_;
v_a_2865_ = v___y_3127_;
v_a_2866_ = v___y_3121_;
v_a_2867_ = v___y_3122_;
v_a_2868_ = v___y_3117_;
v_a_2869_ = v___y_3125_;
v_a_2870_ = v___y_3129_;
v_a_2871_ = v___y_3119_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3133_; 
v_tryPostpone_3133_ = lean_ctor_get_uint8(v_c_x3f_2860_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3133_ == 0)
{
if (v___y_3120_ == 0)
{
lean_object* v_c_3134_; lean_object* v_numCases_3135_; 
v_c_3134_ = lean_ctor_get(v_c_x3f_2860_, 0);
v_numCases_3135_ = lean_ctor_get(v_c_x3f_2860_, 1);
lean_inc_ref(v_c_3134_);
lean_inc(v_numCases_3135_);
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v_numCases_3135_;
v___y_3096_ = v___y_3124_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3125_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v___y_3127_;
v___y_3101_ = v___y_3128_;
v___y_3102_ = v_c_3134_;
v___y_3103_ = v___y_3129_;
v___y_3104_ = v___x_3115_;
goto v___jp_3088_;
}
else
{
lean_dec(v___y_3126_);
v___y_3000_ = v___y_3125_;
v___y_3001_ = v___y_3117_;
v___y_3002_ = v___y_3119_;
v___y_3003_ = v___y_3127_;
v___y_3004_ = v___y_3121_;
v___y_3005_ = v___y_3122_;
v___y_3006_ = v___y_3128_;
v___y_3007_ = v___y_3129_;
v___y_3008_ = v___y_3124_;
v___y_3009_ = v___y_3123_;
goto v___jp_2999_;
}
}
else
{
if (v___y_3120_ == 0)
{
lean_object* v_c_3136_; 
lean_del_object(v___x_2997_);
v_c_3136_ = lean_ctor_get(v_c_x3f_2860_, 0);
lean_inc_ref(v_c_3136_);
lean_dec_ref_known(v_c_x3f_2860_, 2);
v___y_3015_ = v___y_3117_;
v___y_3016_ = v___y_3118_;
v___y_3017_ = v___y_3119_;
v___y_3018_ = v___y_3120_;
v___y_3019_ = v___y_3121_;
v___y_3020_ = v___y_3122_;
v___y_3021_ = v___y_3123_;
v___y_3022_ = v___y_3124_;
v___y_3023_ = v___y_3125_;
v___y_3024_ = v___y_3126_;
v___y_3025_ = v___y_3127_;
v___y_3026_ = v___y_3128_;
v___y_3027_ = v_c_3136_;
v___y_3028_ = v___y_3129_;
goto v___jp_3014_;
}
else
{
if (v___y_3130_ == 0)
{
lean_object* v_c_3137_; lean_object* v_numCases_3138_; 
v_c_3137_ = lean_ctor_get(v_c_x3f_2860_, 0);
v_numCases_3138_ = lean_ctor_get(v_c_x3f_2860_, 1);
lean_inc_ref(v_c_3137_);
lean_inc(v_numCases_3138_);
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v_numCases_3138_;
v___y_3096_ = v___y_3124_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3125_;
v___y_3099_ = v___y_3126_;
v___y_3100_ = v___y_3127_;
v___y_3101_ = v___y_3128_;
v___y_3102_ = v_c_3137_;
v___y_3103_ = v___y_3129_;
v___y_3104_ = v___y_3130_;
goto v___jp_3088_;
}
else
{
lean_object* v_c_3139_; 
lean_del_object(v___x_2997_);
v_c_3139_ = lean_ctor_get(v_c_x3f_2860_, 0);
lean_inc_ref(v_c_3139_);
lean_dec_ref_known(v_c_x3f_2860_, 2);
v___y_3015_ = v___y_3117_;
v___y_3016_ = v___y_3118_;
v___y_3017_ = v___y_3119_;
v___y_3018_ = v___y_3120_;
v___y_3019_ = v___y_3121_;
v___y_3020_ = v___y_3122_;
v___y_3021_ = v___y_3123_;
v___y_3022_ = v___y_3124_;
v___y_3023_ = v___y_3125_;
v___y_3024_ = v___y_3126_;
v___y_3025_ = v___y_3127_;
v___y_3026_ = v___y_3128_;
v___y_3027_ = v_c_3139_;
v___y_3028_ = v___y_3129_;
goto v___jp_3014_;
}
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3151_; 
lean_inc(v_head_2994_);
v___x_3151_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2994_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
switch(lean_obj_tag(v_a_3152_))
{
case 0:
{
lean_del_object(v___x_2997_);
lean_dec(v_head_2994_);
v_cs_2859_ = v_tail_2995_;
v_a_2862_ = v___y_3141_;
v_a_2863_ = v___y_3142_;
v_a_2864_ = v___y_3143_;
v_a_2865_ = v___y_3144_;
v_a_2866_ = v___y_3145_;
v_a_2867_ = v___y_3146_;
v_a_2868_ = v___y_3147_;
v_a_2869_ = v___y_3148_;
v_a_2870_ = v___y_3149_;
v_a_2871_ = v___y_3150_;
goto _start;
}
case 1:
{
lean_object* v___x_3154_; 
lean_del_object(v___x_2997_);
v___x_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_head_2994_);
lean_ctor_set(v___x_3154_, 1, v_cs_x27_2861_);
v_cs_2859_ = v_tail_2995_;
v_cs_x27_2861_ = v___x_3154_;
v_a_2862_ = v___y_3141_;
v_a_2863_ = v___y_3142_;
v_a_2864_ = v___y_3143_;
v_a_2865_ = v___y_3144_;
v_a_2866_ = v___y_3145_;
v_a_2867_ = v___y_3146_;
v_a_2868_ = v___y_3147_;
v_a_2869_ = v___y_3148_;
v_a_2870_ = v___y_3149_;
v_a_2871_ = v___y_3150_;
goto _start;
}
default: 
{
lean_object* v_numCases_3156_; uint8_t v_isRec_3157_; uint8_t v_tryPostpone_3158_; lean_object* v___x_3159_; 
v_numCases_3156_ = lean_ctor_get(v_a_3152_, 0);
lean_inc(v_numCases_3156_);
v_isRec_3157_ = lean_ctor_get_uint8(v_a_3152_, sizeof(void*)*1);
v_tryPostpone_3158_ = lean_ctor_get_uint8(v_a_3152_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3152_, 1);
v___x_3159_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3143_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; uint8_t v___x_3161_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_unbox(v_a_3160_);
lean_dec(v_a_3160_);
if (v___x_3161_ == 0)
{
v___y_3117_ = v___y_3147_;
v___y_3118_ = v_isRec_3157_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v_tryPostpone_3158_;
v___y_3121_ = v___y_3145_;
v___y_3122_ = v___y_3146_;
v___y_3123_ = v___y_3141_;
v___y_3124_ = v___y_3143_;
v___y_3125_ = v___y_3148_;
v___y_3126_ = v_numCases_3156_;
v___y_3127_ = v___y_3144_;
v___y_3128_ = v___y_3142_;
v___y_3129_ = v___y_3149_;
v___y_3130_ = v___x_3115_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = lean_nat_dec_lt(v___x_3162_, v_numCases_3156_);
if (v___x_3163_ == 0)
{
v___y_3117_ = v___y_3147_;
v___y_3118_ = v_isRec_3157_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v_tryPostpone_3158_;
v___y_3121_ = v___y_3145_;
v___y_3122_ = v___y_3146_;
v___y_3123_ = v___y_3141_;
v___y_3124_ = v___y_3143_;
v___y_3125_ = v___y_3148_;
v___y_3126_ = v_numCases_3156_;
v___y_3127_ = v___y_3144_;
v___y_3128_ = v___y_3142_;
v___y_3129_ = v___y_3149_;
v___y_3130_ = v___x_3163_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3164_; 
lean_dec(v_numCases_3156_);
lean_del_object(v___x_2997_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_head_2994_);
lean_ctor_set(v___x_3164_, 1, v_cs_x27_2861_);
v_cs_2859_ = v_tail_2995_;
v_cs_x27_2861_ = v___x_3164_;
v_a_2862_ = v___y_3141_;
v_a_2863_ = v___y_3142_;
v_a_2864_ = v___y_3143_;
v_a_2865_ = v___y_3144_;
v_a_2866_ = v___y_3145_;
v_a_2867_ = v___y_3146_;
v_a_2868_ = v___y_3147_;
v_a_2869_ = v___y_3148_;
v_a_2870_ = v___y_3149_;
v_a_2871_ = v___y_3150_;
goto _start;
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_numCases_3156_);
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3166_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3159_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3159_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3174_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3151_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3151_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3207_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3107_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3107_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
v___jp_2999_:
{
lean_object* v___x_3011_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v_cs_x27_2861_);
v___x_3011_ = v___x_2997_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_head_2994_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_cs_x27_2861_);
v___x_3011_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v_cs_2859_ = v_tail_2995_;
v_cs_x27_2861_ = v___x_3011_;
v_a_2862_ = v___y_3009_;
v_a_2863_ = v___y_3006_;
v_a_2864_ = v___y_3008_;
v_a_2865_ = v___y_3003_;
v_a_2866_ = v___y_3004_;
v_a_2867_ = v___y_3005_;
v_a_2868_ = v___y_3001_;
v_a_2869_ = v___y_3000_;
v_a_2870_ = v___y_3007_;
v_a_2871_ = v___y_3002_;
goto _start;
}
}
v___jp_3014_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3029_, 0, v_head_2994_);
lean_ctor_set(v___x_3029_, 1, v___y_3024_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*2, v___y_3016_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*2 + 1, v___y_3018_);
v___x_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___y_3027_);
lean_ctor_set(v___x_3030_, 1, v_cs_x27_2861_);
v_cs_2859_ = v_tail_2995_;
v_c_x3f_2860_ = v___x_3029_;
v_cs_x27_2861_ = v___x_3030_;
v_a_2862_ = v___y_3021_;
v_a_2863_ = v___y_3026_;
v_a_2864_ = v___y_3022_;
v_a_2865_ = v___y_3025_;
v_a_2866_ = v___y_3019_;
v_a_2867_ = v___y_3020_;
v_a_2868_ = v___y_3015_;
v_a_2869_ = v___y_3023_;
v_a_2870_ = v___y_3028_;
v_a_2871_ = v___y_3017_;
goto _start;
}
v___jp_3032_:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2994_, v___y_3041_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3046_, v___y_3041_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; uint8_t v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = lean_nat_dec_lt(v_a_3049_, v_a_3051_);
lean_dec(v_a_3051_);
lean_dec(v_a_3049_);
if (v___x_3052_ == 0)
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_nat_dec_lt(v___y_3043_, v___y_3039_);
lean_dec(v___y_3039_);
if (v___x_3053_ == 0)
{
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3043_);
v___y_3000_ = v___y_3042_;
v___y_3001_ = v___y_3033_;
v___y_3002_ = v___y_3035_;
v___y_3003_ = v___y_3044_;
v___y_3004_ = v___y_3037_;
v___y_3005_ = v___y_3038_;
v___y_3006_ = v___y_3045_;
v___y_3007_ = v___y_3047_;
v___y_3008_ = v___y_3040_;
v___y_3009_ = v___y_3041_;
goto v___jp_2999_;
}
else
{
lean_del_object(v___x_2997_);
lean_dec(v_c_x3f_2860_);
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3041_;
v___y_3022_ = v___y_3040_;
v___y_3023_ = v___y_3042_;
v___y_3024_ = v___y_3043_;
v___y_3025_ = v___y_3044_;
v___y_3026_ = v___y_3045_;
v___y_3027_ = v___y_3046_;
v___y_3028_ = v___y_3047_;
goto v___jp_3014_;
}
}
else
{
lean_dec(v___y_3039_);
lean_del_object(v___x_2997_);
lean_dec(v_c_x3f_2860_);
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3041_;
v___y_3022_ = v___y_3040_;
v___y_3023_ = v___y_3042_;
v___y_3024_ = v___y_3043_;
v___y_3025_ = v___y_3044_;
v___y_3026_ = v___y_3045_;
v___y_3027_ = v___y_3046_;
v___y_3028_ = v___y_3047_;
goto v___jp_3014_;
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v_a_3049_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3043_);
lean_dec(v___y_3039_);
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3054_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3050_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3050_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3043_);
lean_dec(v___y_3039_);
lean_del_object(v___x_2997_);
lean_dec(v_tail_2995_);
lean_dec(v_head_2994_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
v_a_3062_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3048_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3048_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
v___jp_3070_:
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_dec_lt(v___x_3086_, v___y_3077_);
if (v___x_3087_ == 0)
{
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
v___y_3046_ = v___y_3084_;
v___y_3047_ = v___y_3085_;
goto v___jp_3032_;
}
else
{
lean_dec(v___y_3077_);
lean_del_object(v___x_2997_);
lean_dec(v_c_x3f_2860_);
v___y_3015_ = v___y_3071_;
v___y_3016_ = v___y_3072_;
v___y_3017_ = v___y_3073_;
v___y_3018_ = v___y_3074_;
v___y_3019_ = v___y_3075_;
v___y_3020_ = v___y_3076_;
v___y_3021_ = v___y_3079_;
v___y_3022_ = v___y_3078_;
v___y_3023_ = v___y_3080_;
v___y_3024_ = v___y_3081_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_3084_;
v___y_3028_ = v___y_3085_;
goto v___jp_3014_;
}
}
v___jp_3088_:
{
lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3105_ = lean_unsigned_to_nat(1u);
v___x_3106_ = lean_nat_dec_eq(v___y_3099_, v___x_3105_);
if (v___x_3106_ == 0)
{
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
v___y_3044_ = v___y_3100_;
v___y_3045_ = v___y_3101_;
v___y_3046_ = v___y_3102_;
v___y_3047_ = v___y_3103_;
goto v___jp_3032_;
}
else
{
if (v___y_3090_ == 0)
{
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
v___y_3082_ = v___y_3100_;
v___y_3083_ = v___y_3101_;
v___y_3084_ = v___y_3102_;
v___y_3085_ = v___y_3103_;
goto v___jp_3070_;
}
else
{
if (v___y_3104_ == 0)
{
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
v___y_3044_ = v___y_3100_;
v___y_3045_ = v___y_3101_;
v___y_3046_ = v___y_3102_;
v___y_3047_ = v___y_3103_;
goto v___jp_3032_;
}
else
{
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
v___y_3082_ = v___y_3100_;
v___y_3083_ = v___y_3101_;
v___y_3084_ = v___y_3102_;
v___y_3085_ = v___y_3103_;
goto v___jp_3070_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3216_, lean_object* v_c_x3f_3217_, lean_object* v_cs_x27_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3216_, v_c_x3f_3217_, v_cs_x27_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec(v_a_3219_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3231_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3278_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3278_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3278_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_unbox(v_a_3243_);
lean_dec(v_a_3243_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
lean_del_object(v___x_3245_);
v___x_3248_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3231_, v_a_3233_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3265_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3265_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3265_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_unbox(v_a_3249_);
lean_dec(v_a_3249_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v_toGoalState_3255_; lean_object* v_split_3256_; lean_object* v_candidates_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_del_object(v___x_3251_);
v___x_3254_ = lean_st_ref_get(v_a_3231_);
v_toGoalState_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc_ref(v_toGoalState_3255_);
lean_dec(v___x_3254_);
v_split_3256_ = lean_ctor_get(v_toGoalState_3255_, 15);
lean_inc_ref(v_split_3256_);
lean_dec_ref(v_toGoalState_3255_);
v_candidates_3257_ = lean_ctor_get(v_split_3256_, 1);
lean_inc(v_candidates_3257_);
lean_dec_ref(v_split_3256_);
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_box(0);
v___x_3260_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3257_, v___x_3258_, v___x_3259_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
return v___x_3260_;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3261_ = lean_box(0);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3261_);
v___x_3263_ = v___x_3251_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
v_a_3266_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3248_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3248_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_box(0);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3274_);
v___x_3276_ = v___x_3245_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
v_a_3279_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3242_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3242_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec(v_a_3287_);
return v_res_3298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = lean_box(0);
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3308_ = l_Lean_mkConst(v___x_3307_, v___x_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3309_){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3311_ = l_Lean_Expr_app___override(v___x_3310_, v_c_3309_);
return v___x_3311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_box(0);
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3322_ = l_Lean_mkConst(v___x_3321_, v___x_3320_);
return v___x_3322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_box(0);
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3330_ = l_Lean_mkConst(v___x_3329_, v___x_3328_);
return v___x_3330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = lean_box(0);
v___x_3337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3338_ = l_Lean_mkConst(v___x_3337_, v___x_3336_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___x_3400_; 
lean_inc_ref(v_c_3339_);
v___x_3400_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3339_, v_a_3347_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3473_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3473_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3473_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = l_Lean_Expr_cleanupAnnotations(v_a_3401_);
lean_dec(v_a_3401_);
v___x_3406_ = l_Lean_Expr_isApp(v___x_3405_);
if (v___x_3406_ == 0)
{
lean_dec_ref(v___x_3405_);
lean_del_object(v___x_3403_);
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
goto v___jp_3359_;
}
else
{
lean_object* v_arg_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v_arg_3407_ = lean_ctor_get(v___x_3405_, 1);
lean_inc_ref(v_arg_3407_);
v___x_3408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3405_);
lean_dec_ref(v___x_3405_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3410_ = l_Lean_Expr_isConstOf(v___x_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
uint8_t v___x_3411_; 
v___x_3411_ = l_Lean_Expr_isApp(v___x_3408_);
if (v___x_3411_ == 0)
{
lean_dec_ref(v___x_3408_);
lean_dec_ref(v_arg_3407_);
lean_del_object(v___x_3403_);
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
goto v___jp_3359_;
}
else
{
lean_object* v_arg_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_arg_3412_ = lean_ctor_get(v___x_3408_, 1);
lean_inc_ref(v_arg_3412_);
v___x_3413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3408_);
lean_dec_ref(v___x_3408_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3415_ = l_Lean_Expr_isConstOf(v___x_3413_, v___x_3414_);
if (v___x_3415_ == 0)
{
uint8_t v___x_3416_; 
v___x_3416_ = l_Lean_Expr_isApp(v___x_3413_);
if (v___x_3416_ == 0)
{
lean_dec_ref(v___x_3413_);
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
lean_del_object(v___x_3403_);
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3413_);
lean_dec_ref(v___x_3413_);
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3419_ = l_Lean_Expr_isConstOf(v___x_3417_, v___x_3418_);
lean_dec_ref(v___x_3417_);
if (v___x_3419_ == 0)
{
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
lean_del_object(v___x_3403_);
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
v___y_3366_ = v_a_3346_;
v___y_3367_ = v_a_3347_;
v___y_3368_ = v_a_3348_;
v___y_3369_ = v_a_3349_;
goto v___jp_3359_;
}
else
{
uint8_t v___x_3420_; 
v___x_3420_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3339_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
v___x_3421_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3339_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3421_);
v___x_3423_ = v___x_3403_;
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
else
{
lean_object* v___x_3425_; 
lean_del_object(v___x_3403_);
lean_inc_ref(v_c_3339_);
v___x_3425_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3339_, v_a_3340_, v_a_3344_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; uint8_t v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = lean_unbox(v_a_3426_);
lean_dec(v_a_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3438_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3434_ = l_Lean_mkApp3(v___x_3433_, v_arg_3412_, v_arg_3407_, v_a_3429_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3434_);
v___x_3436_ = v___x_3431_;
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
else
{
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
return v___x_3428_;
}
}
else
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3449_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3449_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3449_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3445_ = l_Lean_mkApp3(v___x_3444_, v_arg_3412_, v_arg_3407_, v_a_3440_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3445_);
v___x_3447_ = v___x_3442_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
return v___x_3439_;
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
lean_dec_ref(v_c_3339_);
v_a_3450_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3425_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3425_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3458_; 
lean_dec_ref(v___x_3413_);
lean_del_object(v___x_3403_);
v___x_3458_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3468_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3464_ = l_Lean_mkApp3(v___x_3463_, v_arg_3412_, v_arg_3407_, v_a_3459_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
else
{
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3407_);
return v___x_3458_;
}
}
}
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
lean_dec_ref(v___x_3408_);
lean_dec_ref(v_c_3339_);
v___x_3469_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3407_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3469_);
v___x_3471_ = v___x_3403_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3339_);
return v___x_3400_;
}
v___jp_3351_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3352_ = lean_unsigned_to_nat(1u);
v___x_3353_ = l_Lean_Expr_getAppNumArgs(v_c_3339_);
v___x_3354_ = lean_nat_sub(v___x_3353_, v___x_3352_);
lean_dec(v___x_3353_);
v___x_3355_ = lean_nat_sub(v___x_3354_, v___x_3352_);
lean_dec(v___x_3354_);
v___x_3356_ = l_Lean_Expr_getRevArg_x21(v_c_3339_, v___x_3355_);
lean_dec_ref(v_c_3339_);
v___x_3357_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
v___jp_3359_:
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_Meta_Grind_isIte(v_c_3339_);
if (v___x_3370_ == 0)
{
uint8_t v___x_3371_; 
v___x_3371_ = l_Lean_Meta_Grind_isDIte(v_c_3339_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
lean_inc_ref(v_c_3339_);
v___x_3372_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3339_, v___y_3360_, v___y_3364_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3391_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3391_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3391_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
uint8_t v___x_3377_; 
v___x_3377_ = lean_unbox(v_a_3373_);
lean_dec(v_a_3373_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3379_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v_c_3339_);
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_c_3339_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
else
{
lean_object* v___x_3381_; 
lean_del_object(v___x_3375_);
lean_inc_ref(v_c_3339_);
v___x_3381_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3339_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3390_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3390_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3390_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3339_, v_a_3382_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3386_);
v___x_3388_ = v___x_3384_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_dec_ref(v_c_3339_);
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v_c_3339_);
v_a_3392_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3372_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3372_);
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
else
{
goto v___jp_3351_;
}
}
else
{
goto v___jp_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec(v_a_3475_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3487_, lean_object* v_major_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3489_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; uint8_t v_trace_3498_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v_trace_3498_ = lean_ctor_get_uint8(v_a_3497_, sizeof(void*)*17);
lean_dec(v_a_3497_);
if (v_trace_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Meta_Grind_cases(v_mvarId_3487_, v_major_3488_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; 
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc_ref(v_major_3488_);
v___x_3500_ = lean_infer_type(v_major_3488_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Meta_whnfD(v_a_3501_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3504_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = l_Lean_Expr_getAppFn(v_a_3503_);
lean_dec(v_a_3503_);
if (lean_obj_tag(v___x_3504_) == 4)
{
lean_object* v_declName_3505_; lean_object* v___x_3506_; 
v_declName_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_declName_3505_);
lean_dec_ref_known(v___x_3504_, 2);
v___x_3506_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3505_, v_a_3490_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; 
lean_dec_ref_known(v___x_3506_, 1);
v___x_3507_ = l_Lean_Meta_Grind_cases(v_mvarId_3487_, v_major_3488_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3507_;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_major_3488_);
lean_dec(v_mvarId_3487_);
v_a_3508_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3506_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v___x_3516_; 
lean_dec_ref(v___x_3504_);
v___x_3516_ = l_Lean_Meta_Grind_cases(v_mvarId_3487_, v_major_3488_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3516_;
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v_major_3488_);
lean_dec(v_mvarId_3487_);
v_a_3517_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3502_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3502_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref(v_major_3488_);
lean_dec(v_mvarId_3487_);
v_a_3525_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3500_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3500_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_major_3488_);
lean_dec(v_mvarId_3487_);
v_a_3533_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3496_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3496_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3541_, lean_object* v_major_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3541_, v_major_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3551_, lean_object* v_major_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3551_, v_major_3552_, v_a_3555_, v_a_3556_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3565_, lean_object* v_major_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3565_, v_major_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec(v_a_3567_);
return v_res_3578_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3579_){
_start:
{
uint64_t v_anchor_3580_; 
v_anchor_3580_ = lean_ctor_get_uint64(v_e_3579_, sizeof(void*)*3);
return v_anchor_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3581_){
_start:
{
uint64_t v_res_3582_; lean_object* v_r_3583_; 
v_res_3582_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3581_);
lean_dec_ref(v_e_3581_);
v_r_3583_ = lean_box_uint64(v_res_3582_);
return v_r_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3586_, lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3587_) == 0)
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_box(0);
return v___x_3588_;
}
else
{
lean_object* v_key_3589_; lean_object* v_value_3590_; lean_object* v_tail_3591_; uint64_t v___x_3592_; uint8_t v___x_3593_; 
v_key_3589_ = lean_ctor_get(v_x_3587_, 0);
v_value_3590_ = lean_ctor_get(v_x_3587_, 1);
v_tail_3591_ = lean_ctor_get(v_x_3587_, 2);
v___x_3592_ = lean_unbox_uint64(v_key_3589_);
v___x_3593_ = lean_uint64_dec_eq(v___x_3592_, v_a_3586_);
if (v___x_3593_ == 0)
{
v_x_3587_ = v_tail_3591_;
goto _start;
}
else
{
lean_object* v___x_3595_; 
lean_inc(v_value_3590_);
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_value_3590_);
return v___x_3595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3596_, lean_object* v_x_3597_){
_start:
{
uint64_t v_a_boxed_3598_; lean_object* v_res_3599_; 
v_a_boxed_3598_ = lean_unbox_uint64(v_a_3596_);
lean_dec_ref(v_a_3596_);
v_res_3599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3598_, v_x_3597_);
lean_dec(v_x_3597_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3600_, uint64_t v_a_3601_){
_start:
{
lean_object* v_buckets_3602_; lean_object* v___x_3603_; uint64_t v___x_3604_; uint64_t v___x_3605_; uint64_t v_fold_3606_; uint64_t v___x_3607_; uint64_t v___x_3608_; uint64_t v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; size_t v___x_3613_; size_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v_buckets_3602_ = lean_ctor_get(v_m_3600_, 1);
v___x_3603_ = lean_array_get_size(v_buckets_3602_);
v___x_3604_ = 32ULL;
v___x_3605_ = lean_uint64_shift_right(v_a_3601_, v___x_3604_);
v_fold_3606_ = lean_uint64_xor(v_a_3601_, v___x_3605_);
v___x_3607_ = 16ULL;
v___x_3608_ = lean_uint64_shift_right(v_fold_3606_, v___x_3607_);
v___x_3609_ = lean_uint64_xor(v_fold_3606_, v___x_3608_);
v___x_3610_ = lean_uint64_to_usize(v___x_3609_);
v___x_3611_ = lean_usize_of_nat(v___x_3603_);
v___x_3612_ = ((size_t)1ULL);
v___x_3613_ = lean_usize_sub(v___x_3611_, v___x_3612_);
v___x_3614_ = lean_usize_land(v___x_3610_, v___x_3613_);
v___x_3615_ = lean_array_uget_borrowed(v_buckets_3602_, v___x_3614_);
v___x_3616_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3601_, v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3617_, lean_object* v_a_3618_){
_start:
{
uint64_t v_a_boxed_3619_; lean_object* v_res_3620_; 
v_a_boxed_3619_ = lean_unbox_uint64(v_a_3618_);
lean_dec_ref(v_a_3618_);
v_res_3620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3617_, v_a_boxed_3619_);
lean_dec_ref(v_m_3617_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
if (lean_obj_tag(v_x_3622_) == 0)
{
return v_x_3621_;
}
else
{
lean_object* v_key_3623_; lean_object* v_value_3624_; lean_object* v_tail_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3649_; 
v_key_3623_ = lean_ctor_get(v_x_3622_, 0);
v_value_3624_ = lean_ctor_get(v_x_3622_, 1);
v_tail_3625_ = lean_ctor_get(v_x_3622_, 2);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_x_3622_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3627_ = v_x_3622_;
v_isShared_3628_ = v_isSharedCheck_3649_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_tail_3625_);
lean_inc(v_value_3624_);
lean_inc(v_key_3623_);
lean_dec(v_x_3622_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3649_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; uint64_t v___x_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v___x_3633_; uint64_t v_fold_3634_; uint64_t v___x_3635_; uint64_t v___x_3636_; uint64_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; size_t v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3629_ = lean_array_get_size(v_x_3621_);
v___x_3630_ = 32ULL;
v___x_3631_ = lean_unbox_uint64(v_key_3623_);
v___x_3632_ = lean_uint64_shift_right(v___x_3631_, v___x_3630_);
v___x_3633_ = lean_unbox_uint64(v_key_3623_);
v_fold_3634_ = lean_uint64_xor(v___x_3633_, v___x_3632_);
v___x_3635_ = 16ULL;
v___x_3636_ = lean_uint64_shift_right(v_fold_3634_, v___x_3635_);
v___x_3637_ = lean_uint64_xor(v_fold_3634_, v___x_3636_);
v___x_3638_ = lean_uint64_to_usize(v___x_3637_);
v___x_3639_ = lean_usize_of_nat(v___x_3629_);
v___x_3640_ = ((size_t)1ULL);
v___x_3641_ = lean_usize_sub(v___x_3639_, v___x_3640_);
v___x_3642_ = lean_usize_land(v___x_3638_, v___x_3641_);
v___x_3643_ = lean_array_uget_borrowed(v_x_3621_, v___x_3642_);
lean_inc(v___x_3643_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 2, v___x_3643_);
v___x_3645_ = v___x_3627_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_key_3623_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_value_3624_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_array_uset(v_x_3621_, v___x_3642_, v___x_3645_);
v_x_3621_ = v___x_3646_;
v_x_3622_ = v_tail_3625_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3650_, lean_object* v_source_3651_, lean_object* v_target_3652_){
_start:
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = lean_array_get_size(v_source_3651_);
v___x_3654_ = lean_nat_dec_lt(v_i_3650_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_dec_ref(v_source_3651_);
lean_dec(v_i_3650_);
return v_target_3652_;
}
else
{
lean_object* v_es_3655_; lean_object* v___x_3656_; lean_object* v_source_3657_; lean_object* v_target_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v_es_3655_ = lean_array_fget(v_source_3651_, v_i_3650_);
v___x_3656_ = lean_box(0);
v_source_3657_ = lean_array_fset(v_source_3651_, v_i_3650_, v___x_3656_);
v_target_3658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3652_, v_es_3655_);
v___x_3659_ = lean_unsigned_to_nat(1u);
v___x_3660_ = lean_nat_add(v_i_3650_, v___x_3659_);
lean_dec(v_i_3650_);
v_i_3650_ = v___x_3660_;
v_source_3651_ = v_source_3657_;
v_target_3652_ = v_target_3658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3662_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v_nbuckets_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3663_ = lean_array_get_size(v_data_3662_);
v___x_3664_ = lean_unsigned_to_nat(2u);
v_nbuckets_3665_ = lean_nat_mul(v___x_3663_, v___x_3664_);
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_mk_array(v_nbuckets_3665_, v___x_3667_);
v___x_3669_ = lean_array_propagate_mark(v_data_3662_, v___x_3668_);
v___x_3670_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3666_, v_data_3662_, v___x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3671_, lean_object* v_b_3672_, lean_object* v_x_3673_){
_start:
{
if (lean_obj_tag(v_x_3673_) == 0)
{
lean_dec(v_b_3672_);
return v_x_3673_;
}
else
{
lean_object* v_key_3674_; lean_object* v_value_3675_; lean_object* v_tail_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3690_; 
v_key_3674_ = lean_ctor_get(v_x_3673_, 0);
v_value_3675_ = lean_ctor_get(v_x_3673_, 1);
v_tail_3676_ = lean_ctor_get(v_x_3673_, 2);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_x_3673_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3678_ = v_x_3673_;
v_isShared_3679_ = v_isSharedCheck_3690_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_tail_3676_);
lean_inc(v_value_3675_);
lean_inc(v_key_3674_);
lean_dec(v_x_3673_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3690_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
uint64_t v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = lean_unbox_uint64(v_key_3674_);
v___x_3681_ = lean_uint64_dec_eq(v___x_3680_, v_a_3671_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3671_, v_b_3672_, v_tail_3676_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 2, v___x_3682_);
v___x_3684_ = v___x_3678_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_key_3674_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_value_3675_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
lean_dec(v_value_3675_);
lean_dec(v_key_3674_);
v___x_3686_ = lean_box_uint64(v_a_3671_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 1, v_b_3672_);
lean_ctor_set(v___x_3678_, 0, v___x_3686_);
v___x_3688_ = v___x_3678_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_b_3672_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_tail_3676_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3691_, lean_object* v_b_3692_, lean_object* v_x_3693_){
_start:
{
uint64_t v_a_boxed_3694_; lean_object* v_res_3695_; 
v_a_boxed_3694_ = lean_unbox_uint64(v_a_3691_);
lean_dec_ref(v_a_3691_);
v_res_3695_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3694_, v_b_3692_, v_x_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3696_, lean_object* v_x_3697_){
_start:
{
if (lean_obj_tag(v_x_3697_) == 0)
{
uint8_t v___x_3698_; 
v___x_3698_ = 0;
return v___x_3698_;
}
else
{
lean_object* v_key_3699_; lean_object* v_tail_3700_; uint64_t v___x_3701_; uint8_t v___x_3702_; 
v_key_3699_ = lean_ctor_get(v_x_3697_, 0);
v_tail_3700_ = lean_ctor_get(v_x_3697_, 2);
v___x_3701_ = lean_unbox_uint64(v_key_3699_);
v___x_3702_ = lean_uint64_dec_eq(v___x_3701_, v_a_3696_);
if (v___x_3702_ == 0)
{
v_x_3697_ = v_tail_3700_;
goto _start;
}
else
{
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3704_, lean_object* v_x_3705_){
_start:
{
uint64_t v_a_boxed_3706_; uint8_t v_res_3707_; lean_object* v_r_3708_; 
v_a_boxed_3706_ = lean_unbox_uint64(v_a_3704_);
lean_dec_ref(v_a_3704_);
v_res_3707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3706_, v_x_3705_);
lean_dec(v_x_3705_);
v_r_3708_ = lean_box(v_res_3707_);
return v_r_3708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3709_, uint64_t v_a_3710_, lean_object* v_b_3711_){
_start:
{
lean_object* v_size_3712_; lean_object* v_buckets_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3756_; 
v_size_3712_ = lean_ctor_get(v_m_3709_, 0);
v_buckets_3713_ = lean_ctor_get(v_m_3709_, 1);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_m_3709_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3715_ = v_m_3709_;
v_isShared_3716_ = v_isSharedCheck_3756_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_buckets_3713_);
lean_inc(v_size_3712_);
lean_dec(v_m_3709_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3756_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; uint64_t v___x_3718_; uint64_t v___x_3719_; uint64_t v_fold_3720_; uint64_t v___x_3721_; uint64_t v___x_3722_; uint64_t v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; size_t v___x_3727_; size_t v___x_3728_; lean_object* v_bkt_3729_; uint8_t v___x_3730_; 
v___x_3717_ = lean_array_get_size(v_buckets_3713_);
v___x_3718_ = 32ULL;
v___x_3719_ = lean_uint64_shift_right(v_a_3710_, v___x_3718_);
v_fold_3720_ = lean_uint64_xor(v_a_3710_, v___x_3719_);
v___x_3721_ = 16ULL;
v___x_3722_ = lean_uint64_shift_right(v_fold_3720_, v___x_3721_);
v___x_3723_ = lean_uint64_xor(v_fold_3720_, v___x_3722_);
v___x_3724_ = lean_uint64_to_usize(v___x_3723_);
v___x_3725_ = lean_usize_of_nat(v___x_3717_);
v___x_3726_ = ((size_t)1ULL);
v___x_3727_ = lean_usize_sub(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_usize_land(v___x_3724_, v___x_3727_);
v_bkt_3729_ = lean_array_uget_borrowed(v_buckets_3713_, v___x_3728_);
v___x_3730_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3710_, v_bkt_3729_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v_size_x27_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v_buckets_x27_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3731_ = lean_unsigned_to_nat(1u);
v_size_x27_3732_ = lean_nat_add(v_size_3712_, v___x_3731_);
lean_dec(v_size_3712_);
v___x_3733_ = lean_box_uint64(v_a_3710_);
lean_inc(v_bkt_3729_);
v___x_3734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
lean_ctor_set(v___x_3734_, 1, v_b_3711_);
lean_ctor_set(v___x_3734_, 2, v_bkt_3729_);
v_buckets_x27_3735_ = lean_array_uset(v_buckets_3713_, v___x_3728_, v___x_3734_);
v___x_3736_ = lean_unsigned_to_nat(4u);
v___x_3737_ = lean_nat_mul(v_size_x27_3732_, v___x_3736_);
v___x_3738_ = lean_unsigned_to_nat(3u);
v___x_3739_ = lean_nat_div(v___x_3737_, v___x_3738_);
lean_dec(v___x_3737_);
v___x_3740_ = lean_array_get_size(v_buckets_x27_3735_);
v___x_3741_ = lean_nat_dec_le(v___x_3739_, v___x_3740_);
lean_dec(v___x_3739_);
if (v___x_3741_ == 0)
{
lean_object* v_val_3742_; lean_object* v___x_3744_; 
v_val_3742_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3735_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 1, v_val_3742_);
lean_ctor_set(v___x_3715_, 0, v_size_x27_3732_);
v___x_3744_ = v___x_3715_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_size_x27_3732_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_val_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
else
{
lean_object* v___x_3747_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 1, v_buckets_x27_3735_);
lean_ctor_set(v___x_3715_, 0, v_size_x27_3732_);
v___x_3747_ = v___x_3715_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_size_x27_3732_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_buckets_x27_3735_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
else
{
lean_object* v___x_3749_; lean_object* v_buckets_x27_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
lean_inc(v_bkt_3729_);
v___x_3749_ = lean_box(0);
v_buckets_x27_3750_ = lean_array_uset(v_buckets_3713_, v___x_3728_, v___x_3749_);
v___x_3751_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3710_, v_b_3711_, v_bkt_3729_);
v___x_3752_ = lean_array_uset(v_buckets_x27_3750_, v___x_3728_, v___x_3751_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 1, v___x_3752_);
v___x_3754_ = v___x_3715_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_size_3712_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3757_, lean_object* v_a_3758_, lean_object* v_b_3759_){
_start:
{
uint64_t v_a_boxed_3760_; lean_object* v_res_3761_; 
v_a_boxed_3760_ = lean_unbox_uint64(v_a_3758_);
lean_dec_ref(v_a_3758_);
v_res_3761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3757_, v_a_boxed_3760_, v_b_3759_);
return v_res_3761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_unsigned_to_nat(16u);
v___x_3764_ = lean_mk_array(v___x_3763_, v___x_3762_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v_found_3767_; 
v___x_3765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3766_ = lean_unsigned_to_nat(0u);
v_found_3767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3767_, 0, v___x_3766_);
lean_ctor_set(v_found_3767_, 1, v___x_3765_);
return v_found_3767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_found_3768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v_found_3768_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3771_, lean_object* v_numDigits_3772_, lean_object* v_es_3773_, lean_object* v_as_3774_, size_t v_sz_3775_, size_t v_i_3776_, lean_object* v_b_3777_){
_start:
{
lean_object* v_a_3779_; uint8_t v___x_3783_; 
v___x_3783_ = lean_usize_dec_lt(v_i_3776_, v_sz_3775_);
if (v___x_3783_ == 0)
{
return v_b_3777_;
}
else
{
lean_object* v_snd_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3818_; 
v_snd_3784_ = lean_ctor_get(v_b_3777_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_b_3777_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v_b_3777_, 0);
lean_dec(v_unused_3819_);
v___x_3786_ = v_b_3777_;
v_isShared_3787_ = v_isSharedCheck_3818_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_snd_3784_);
lean_dec(v_b_3777_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3818_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v_a_3788_; uint64_t v_anchor_3789_; lean_object* v___x_3790_; uint64_t v___x_3791_; uint64_t v___x_3792_; lean_object* v___x_3793_; 
v_a_3788_ = lean_array_uget_borrowed(v_as_3774_, v_i_3776_);
v_anchor_3789_ = lean_ctor_get_uint64(v_a_3788_, sizeof(void*)*3);
v___x_3790_ = lean_box(0);
v___x_3791_ = lean_uint64_of_nat(v_shift_3771_);
v___x_3792_ = lean_uint64_shift_right(v_anchor_3789_, v___x_3791_);
v___x_3793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3784_, v___x_3792_);
if (lean_obj_tag(v___x_3793_) == 1)
{
lean_object* v_val_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3812_; 
v_val_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3812_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_val_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3812_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
uint64_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = lean_unbox_uint64(v_val_3794_);
lean_dec(v_val_3794_);
v___x_3799_ = lean_uint64_dec_eq(v___x_3798_, v_anchor_3789_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3800_ = lean_unsigned_to_nat(1u);
v___x_3801_ = lean_nat_add(v_numDigits_3772_, v___x_3800_);
v___x_3802_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3773_, v___x_3801_);
lean_dec(v___x_3801_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3802_);
v___x_3804_ = v___x_3796_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3806_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3804_);
v___x_3806_ = v___x_3786_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_snd_3784_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
else
{
lean_object* v___x_3810_; 
lean_del_object(v___x_3796_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3790_);
v___x_3810_ = v___x_3786_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_snd_3784_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
v_a_3779_ = v___x_3810_;
goto v___jp_3778_;
}
}
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_dec(v___x_3793_);
v___x_3813_ = lean_box_uint64(v_anchor_3789_);
v___x_3814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3784_, v___x_3792_, v___x_3813_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 1, v___x_3814_);
lean_ctor_set(v___x_3786_, 0, v___x_3790_);
v___x_3816_ = v___x_3786_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
v_a_3779_ = v___x_3816_;
goto v___jp_3778_;
}
}
}
}
v___jp_3778_:
{
size_t v___x_3780_; size_t v___x_3781_; 
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3776_, v___x_3780_);
v_i_3776_ = v___x_3781_;
v_b_3777_ = v_a_3779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3820_, lean_object* v_numDigits_3821_){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v___x_3822_ = lean_unsigned_to_nat(4u);
v___x_3823_ = lean_nat_mul(v___x_3822_, v_numDigits_3821_);
v___x_3824_ = lean_unsigned_to_nat(64u);
v___x_3825_ = lean_nat_dec_lt(v___x_3823_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_dec(v___x_3823_);
lean_inc(v_numDigits_3821_);
return v_numDigits_3821_;
}
else
{
lean_object* v_shift_3826_; lean_object* v___x_3827_; size_t v_sz_3828_; size_t v___x_3829_; lean_object* v___x_3830_; lean_object* v_fst_3831_; 
v_shift_3826_ = lean_nat_sub(v___x_3824_, v___x_3823_);
lean_dec(v___x_3823_);
v___x_3827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3828_ = lean_array_size(v_es_3820_);
v___x_3829_ = ((size_t)0ULL);
v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3826_, v_numDigits_3821_, v_es_3820_, v_es_3820_, v_sz_3828_, v___x_3829_, v___x_3827_);
lean_dec(v_shift_3826_);
v_fst_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_fst_3831_);
lean_dec_ref(v___x_3830_);
if (lean_obj_tag(v_fst_3831_) == 0)
{
lean_inc(v_numDigits_3821_);
return v_numDigits_3821_;
}
else
{
lean_object* v_val_3832_; 
v_val_3832_ = lean_ctor_get(v_fst_3831_, 0);
lean_inc(v_val_3832_);
lean_dec_ref_known(v_fst_3831_, 1);
return v_val_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3833_, lean_object* v_numDigits_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3833_, v_numDigits_3834_);
lean_dec(v_numDigits_3834_);
lean_dec_ref(v_es_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3836_, lean_object* v_numDigits_3837_, lean_object* v_es_3838_, lean_object* v_as_3839_, lean_object* v_sz_3840_, lean_object* v_i_3841_, lean_object* v_b_3842_){
_start:
{
size_t v_sz_boxed_3843_; size_t v_i_boxed_3844_; lean_object* v_res_3845_; 
v_sz_boxed_3843_ = lean_unbox_usize(v_sz_3840_);
lean_dec(v_sz_3840_);
v_i_boxed_3844_ = lean_unbox_usize(v_i_3841_);
lean_dec(v_i_3841_);
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3836_, v_numDigits_3837_, v_es_3838_, v_as_3839_, v_sz_boxed_3843_, v_i_boxed_3844_, v_b_3842_);
lean_dec_ref(v_as_3839_);
lean_dec_ref(v_es_3838_);
lean_dec(v_numDigits_3837_);
lean_dec(v_shift_3836_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3846_){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = lean_unsigned_to_nat(4u);
v___x_3848_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3846_, v___x_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3849_);
lean_dec_ref(v_es_3849_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3851_, lean_object* v_as_3852_, size_t v_i_3853_, size_t v_stop_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_a_3868_; uint8_t v___x_3872_; 
v___x_3872_ = lean_usize_dec_eq(v_i_3853_, v_stop_3854_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v_e_3874_; lean_object* v___x_3875_; 
v___x_3873_ = lean_array_uget_borrowed(v_as_3852_, v_i_3853_);
v_e_3874_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3873_);
v___x_3875_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3873_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
lean_inc(v___x_3873_);
v___x_3877_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3873_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
if (lean_obj_tag(v_a_3878_) == 2)
{
lean_object* v_numCases_3879_; uint8_t v_isRec_3880_; lean_object* v___x_3881_; 
v_numCases_3879_ = lean_ctor_get(v_a_3878_, 0);
lean_inc(v_numCases_3879_);
v_isRec_3880_ = lean_ctor_get_uint8(v_a_3878_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3878_, 1);
lean_inc_ref(v_filter_3851_);
lean_inc(v___y_3865_);
lean_inc_ref(v___y_3864_);
lean_inc(v___y_3863_);
lean_inc_ref(v___y_3862_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc(v___y_3856_);
lean_inc_ref(v_e_3874_);
v___x_3881_ = lean_apply_12(v_filter_3851_, v_e_3874_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, lean_box(0));
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; uint8_t v___x_3883_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = lean_unbox(v_a_3882_);
lean_dec(v_a_3882_);
if (v___x_3883_ == 0)
{
lean_dec(v_numCases_3879_);
lean_dec(v_a_3876_);
lean_dec_ref(v_e_3874_);
v_a_3868_ = v_b_3855_;
goto v___jp_3867_;
}
else
{
lean_object* v___x_3884_; uint64_t v___x_3885_; lean_object* v___x_3886_; 
lean_inc(v___x_3873_);
v___x_3884_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3884_, 0, v___x_3873_);
lean_ctor_set(v___x_3884_, 1, v_numCases_3879_);
lean_ctor_set(v___x_3884_, 2, v_e_3874_);
lean_ctor_set_uint8(v___x_3884_, sizeof(void*)*3 + 8, v_isRec_3880_);
v___x_3885_ = lean_unbox_uint64(v_a_3876_);
lean_dec(v_a_3876_);
lean_ctor_set_uint64(v___x_3884_, sizeof(void*)*3, v___x_3885_);
v___x_3886_ = lean_array_push(v_b_3855_, v___x_3884_);
v_a_3868_ = v___x_3886_;
goto v___jp_3867_;
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec(v_numCases_3879_);
lean_dec(v_a_3876_);
lean_dec_ref(v_e_3874_);
lean_dec_ref(v_b_3855_);
lean_dec_ref(v_filter_3851_);
v_a_3887_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3881_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3881_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_dec(v_a_3878_);
lean_dec(v_a_3876_);
lean_dec_ref(v_e_3874_);
v_a_3868_ = v_b_3855_;
goto v___jp_3867_;
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_a_3876_);
lean_dec_ref(v_e_3874_);
lean_dec_ref(v_b_3855_);
lean_dec_ref(v_filter_3851_);
v_a_3895_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3877_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3877_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec_ref(v_e_3874_);
lean_dec_ref(v_b_3855_);
lean_dec_ref(v_filter_3851_);
v_a_3903_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3875_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3875_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
lean_object* v___x_3911_; 
lean_dec_ref(v_filter_3851_);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v_b_3855_);
return v___x_3911_;
}
v___jp_3867_:
{
size_t v___x_3869_; size_t v___x_3870_; 
v___x_3869_ = ((size_t)1ULL);
v___x_3870_ = lean_usize_add(v_i_3853_, v___x_3869_);
v_i_3853_ = v___x_3870_;
v_b_3855_ = v_a_3868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3912_, lean_object* v_as_3913_, lean_object* v_i_3914_, lean_object* v_stop_3915_, lean_object* v_b_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
size_t v_i_boxed_3928_; size_t v_stop_boxed_3929_; lean_object* v_res_3930_; 
v_i_boxed_3928_ = lean_unbox_usize(v_i_3914_);
lean_dec(v_i_3914_);
v_stop_boxed_3929_ = lean_unbox_usize(v_stop_3915_);
lean_dec(v_stop_3915_);
v_res_3930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3912_, v_as_3913_, v_i_boxed_3928_, v_stop_boxed_3929_, v_b_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v_as_3913_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3933_, lean_object* v_as_3934_, lean_object* v_start_3935_, lean_object* v_stop_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3948_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3949_ = lean_nat_dec_lt(v_start_3935_, v_stop_3936_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
lean_dec_ref(v_filter_3933_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3951_ = lean_array_get_size(v_as_3934_);
v___x_3952_ = lean_nat_dec_le(v_stop_3936_, v___x_3951_);
if (v___x_3952_ == 0)
{
uint8_t v___x_3953_; 
v___x_3953_ = lean_nat_dec_lt(v_start_3935_, v___x_3951_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v_filter_3933_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3948_);
return v___x_3954_;
}
else
{
size_t v___x_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
v___x_3955_ = lean_usize_of_nat(v_start_3935_);
v___x_3956_ = lean_usize_of_nat(v___x_3951_);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3933_, v_as_3934_, v___x_3955_, v___x_3956_, v___x_3948_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3957_;
}
}
else
{
size_t v___x_3958_; size_t v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = lean_usize_of_nat(v_start_3935_);
v___x_3959_ = lean_usize_of_nat(v_stop_3936_);
v___x_3960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3933_, v_as_3934_, v___x_3958_, v___x_3959_, v___x_3948_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3961_, lean_object* v_as_3962_, lean_object* v_start_3963_, lean_object* v_stop_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3961_, v_as_3962_, v_start_3963_, v_stop_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v_stop_3964_);
lean_dec(v_start_3963_);
lean_dec_ref(v_as_3962_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3977_, lean_object* v_candidates_x3f_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_candidates_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; 
if (lean_obj_tag(v_candidates_x3f_3978_) == 0)
{
lean_object* v___x_4024_; lean_object* v_toGoalState_4025_; lean_object* v_split_4026_; lean_object* v_candidates_4027_; 
v___x_4024_ = lean_st_ref_get(v_a_3979_);
v_toGoalState_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc_ref(v_toGoalState_4025_);
lean_dec(v___x_4024_);
v_split_4026_ = lean_ctor_get(v_toGoalState_4025_, 15);
lean_inc_ref(v_split_4026_);
lean_dec_ref(v_toGoalState_4025_);
v_candidates_4027_ = lean_ctor_get(v_split_4026_, 1);
lean_inc(v_candidates_4027_);
lean_dec_ref(v_split_4026_);
v_candidates_3991_ = v_candidates_4027_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
goto v___jp_3990_;
}
else
{
lean_object* v_val_4028_; 
v_val_4028_ = lean_ctor_get(v_candidates_x3f_3978_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_candidates_x3f_3978_, 1);
v_candidates_3991_ = v_val_4028_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
goto v___jp_3990_;
}
v___jp_3990_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4002_ = lean_array_mk(v_candidates_3991_);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = lean_array_get_size(v___x_4002_);
v___x_4005_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3977_, v___x_4002_, v___x_4003_, v___x_4004_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
lean_dec_ref(v___x_4002_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4015_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4015_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4015_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4010_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4006_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v_a_4006_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4011_);
v___x_4013_ = v___x_4008_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
v_a_4016_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4005_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4005_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4029_, lean_object* v_candidates_x3f_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4029_, v_candidates_x3f_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec(v_a_4031_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4043_, lean_object* v_m_4044_, uint64_t v_a_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4044_, v_a_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4047_, lean_object* v_m_4048_, lean_object* v_a_4049_){
_start:
{
uint64_t v_a_boxed_4050_; lean_object* v_res_4051_; 
v_a_boxed_4050_ = lean_unbox_uint64(v_a_4049_);
lean_dec_ref(v_a_4049_);
v_res_4051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4047_, v_m_4048_, v_a_boxed_4050_);
lean_dec_ref(v_m_4048_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4052_, lean_object* v_m_4053_, uint64_t v_a_4054_, lean_object* v_b_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4053_, v_a_4054_, v_b_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4057_, lean_object* v_m_4058_, lean_object* v_a_4059_, lean_object* v_b_4060_){
_start:
{
uint64_t v_a_boxed_4061_; lean_object* v_res_4062_; 
v_a_boxed_4061_ = lean_unbox_uint64(v_a_4059_);
lean_dec_ref(v_a_4059_);
v_res_4062_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4057_, v_m_4058_, v_a_boxed_4061_, v_b_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4063_, uint64_t v_a_4064_, lean_object* v_x_4065_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4064_, v_x_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4067_, lean_object* v_a_4068_, lean_object* v_x_4069_){
_start:
{
uint64_t v_a_boxed_4070_; lean_object* v_res_4071_; 
v_a_boxed_4070_ = lean_unbox_uint64(v_a_4068_);
lean_dec_ref(v_a_4068_);
v_res_4071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4067_, v_a_boxed_4070_, v_x_4069_);
lean_dec(v_x_4069_);
return v_res_4071_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4072_, uint64_t v_a_4073_, lean_object* v_x_4074_){
_start:
{
uint8_t v___x_4075_; 
v___x_4075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4073_, v_x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4076_, lean_object* v_a_4077_, lean_object* v_x_4078_){
_start:
{
uint64_t v_a_boxed_4079_; uint8_t v_res_4080_; lean_object* v_r_4081_; 
v_a_boxed_4079_ = lean_unbox_uint64(v_a_4077_);
lean_dec_ref(v_a_4077_);
v_res_4080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4076_, v_a_boxed_4079_, v_x_4078_);
lean_dec(v_x_4078_);
v_r_4081_ = lean_box(v_res_4080_);
return v_r_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4082_, lean_object* v_data_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4085_, uint64_t v_a_4086_, lean_object* v_b_4087_, lean_object* v_x_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4086_, v_b_4087_, v_x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4090_, lean_object* v_a_4091_, lean_object* v_b_4092_, lean_object* v_x_4093_){
_start:
{
uint64_t v_a_boxed_4094_; lean_object* v_res_4095_; 
v_a_boxed_4094_ = lean_unbox_uint64(v_a_4091_);
lean_dec_ref(v_a_4091_);
v_res_4095_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4090_, v_a_boxed_4094_, v_b_4092_, v_x_4093_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4096_, lean_object* v_i_4097_, lean_object* v_source_4098_, lean_object* v_target_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4097_, v_source_4098_, v_target_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4101_, lean_object* v_x_4102_, lean_object* v_x_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4102_, v_x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = 1;
v___x_4118_ = lean_box(v___x_4117_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v_x_4120_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4133_, uint64_t v_a_4134_, lean_object* v_c_4135_, lean_object* v_numDigits_4136_, lean_object* v_as_4137_, size_t v_sz_4138_, size_t v_i_4139_, lean_object* v_b_4140_){
_start:
{
lean_object* v_a_4143_; uint8_t v___x_4147_; 
v___x_4147_ = lean_usize_dec_lt(v_i_4139_, v_sz_4138_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; 
lean_dec(v_numDigits_4136_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v_b_4140_);
return v___x_4148_;
}
else
{
lean_object* v_snd_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4175_; 
v_snd_4149_ = lean_ctor_get(v_b_4140_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_b_4140_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; 
v_unused_4176_ = lean_ctor_get(v_b_4140_, 0);
lean_dec(v_unused_4176_);
v___x_4151_ = v_b_4140_;
v_isShared_4152_ = v_isSharedCheck_4175_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_snd_4149_);
lean_dec(v_b_4140_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4175_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v_a_4153_; lean_object* v_c_4154_; uint64_t v_anchor_4155_; lean_object* v___x_4156_; uint64_t v___x_4157_; uint64_t v___x_4158_; uint8_t v___x_4159_; 
v_a_4153_ = lean_array_uget_borrowed(v_as_4137_, v_i_4139_);
v_c_4154_ = lean_ctor_get(v_a_4153_, 0);
v_anchor_4155_ = lean_ctor_get_uint64(v_a_4153_, sizeof(void*)*3);
v___x_4156_ = lean_box(0);
v___x_4157_ = lean_uint64_shift_right(v_anchor_4155_, v___x_4133_);
v___x_4158_ = lean_uint64_shift_right(v_a_4134_, v___x_4133_);
v___x_4159_ = lean_uint64_dec_eq(v___x_4157_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4161_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4156_);
v___x_4161_ = v___x_4151_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4156_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v_snd_4149_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
v_a_4143_ = v___x_4161_;
goto v___jp_4142_;
}
}
else
{
uint8_t v___x_4163_; 
v___x_4163_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4154_, v_c_4135_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4164_ = lean_unsigned_to_nat(1u);
v___x_4165_ = lean_nat_add(v_snd_4149_, v___x_4164_);
lean_dec(v_snd_4149_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 1, v___x_4165_);
lean_ctor_set(v___x_4151_, 0, v___x_4156_);
v___x_4167_ = v___x_4151_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4156_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
v_a_4143_ = v___x_4167_;
goto v___jp_4142_;
}
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_inc(v_snd_4149_);
v___x_4169_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4169_, 0, v_numDigits_4136_);
lean_ctor_set(v___x_4169_, 1, v_snd_4149_);
lean_ctor_set_uint64(v___x_4169_, sizeof(void*)*2, v_a_4134_);
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4170_);
v___x_4172_ = v___x_4151_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4170_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v_snd_4149_);
v___x_4172_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; 
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
return v___x_4173_;
}
}
}
}
}
v___jp_4142_:
{
size_t v___x_4144_; size_t v___x_4145_; 
v___x_4144_ = ((size_t)1ULL);
v___x_4145_ = lean_usize_add(v_i_4139_, v___x_4144_);
v_i_4139_ = v___x_4145_;
v_b_4140_ = v_a_4143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4177_, lean_object* v_a_4178_, lean_object* v_c_4179_, lean_object* v_numDigits_4180_, lean_object* v_as_4181_, lean_object* v_sz_4182_, lean_object* v_i_4183_, lean_object* v_b_4184_, lean_object* v___y_4185_){
_start:
{
uint64_t v___x_7695__boxed_4186_; uint64_t v_a_7696__boxed_4187_; size_t v_sz_boxed_4188_; size_t v_i_boxed_4189_; lean_object* v_res_4190_; 
v___x_7695__boxed_4186_ = lean_unbox_uint64(v___x_4177_);
lean_dec_ref(v___x_4177_);
v_a_7696__boxed_4187_ = lean_unbox_uint64(v_a_4178_);
lean_dec_ref(v_a_4178_);
v_sz_boxed_4188_ = lean_unbox_usize(v_sz_4182_);
lean_dec(v_sz_4182_);
v_i_boxed_4189_ = lean_unbox_usize(v_i_4183_);
lean_dec(v_i_4183_);
v_res_4190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7695__boxed_4186_, v_a_7696__boxed_4187_, v_c_4179_, v_numDigits_4180_, v_as_4181_, v_sz_boxed_4188_, v_i_boxed_4189_, v_b_4184_);
lean_dec_ref(v_as_4181_);
lean_dec_ref(v_c_4179_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4195_, lean_object* v_candidates_x3f_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v___f_4208_; lean_object* v___x_4209_; 
v___f_4208_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4209_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4208_, v_candidates_x3f_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v_candidates_4211_; lean_object* v_numDigits_4212_; lean_object* v___x_4213_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v_candidates_4211_ = lean_ctor_get(v_a_4210_, 0);
lean_inc_ref(v_candidates_4211_);
v_numDigits_4212_ = lean_ctor_get(v_a_4210_, 1);
lean_inc(v_numDigits_4212_);
lean_dec(v_a_4210_);
v___x_4213_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4195_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; uint64_t v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; size_t v_sz_4222_; size_t v___x_4223_; uint64_t v___x_4224_; lean_object* v___x_4225_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4215_ = lean_unsigned_to_nat(64u);
v___x_4216_ = lean_unsigned_to_nat(4u);
v___x_4217_ = lean_nat_mul(v___x_4216_, v_numDigits_4212_);
v___x_4218_ = lean_nat_sub(v___x_4215_, v___x_4217_);
lean_dec(v___x_4217_);
v___x_4219_ = lean_uint64_of_nat(v___x_4218_);
lean_dec(v___x_4218_);
v___x_4220_ = lean_unsigned_to_nat(0u);
v___x_4221_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4222_ = lean_array_size(v_candidates_4211_);
v___x_4223_ = ((size_t)0ULL);
v___x_4224_ = lean_unbox_uint64(v_a_4214_);
lean_inc(v_numDigits_4212_);
v___x_4225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4219_, v___x_4224_, v_c_4195_, v_numDigits_4212_, v_candidates_4211_, v_sz_4222_, v___x_4223_, v___x_4221_);
lean_dec_ref(v_candidates_4211_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4240_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4228_ = v___x_4225_;
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v_fst_4230_; 
v_fst_4230_ = lean_ctor_get(v_a_4226_, 0);
lean_inc(v_fst_4230_);
lean_dec(v_a_4226_);
if (lean_obj_tag(v_fst_4230_) == 0)
{
lean_object* v___x_4231_; uint64_t v___x_4232_; lean_object* v___x_4234_; 
v___x_4231_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4231_, 0, v_numDigits_4212_);
lean_ctor_set(v___x_4231_, 1, v___x_4220_);
v___x_4232_ = lean_unbox_uint64(v_a_4214_);
lean_dec(v_a_4214_);
lean_ctor_set_uint64(v___x_4231_, sizeof(void*)*2, v___x_4232_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4231_);
v___x_4234_ = v___x_4228_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4231_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
else
{
lean_object* v_val_4236_; lean_object* v___x_4238_; 
lean_dec(v_a_4214_);
lean_dec(v_numDigits_4212_);
v_val_4236_ = lean_ctor_get(v_fst_4230_, 0);
lean_inc(v_val_4236_);
lean_dec_ref_known(v_fst_4230_, 1);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v_val_4236_);
v___x_4238_ = v___x_4228_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_val_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec(v_a_4214_);
lean_dec(v_numDigits_4212_);
v_a_4241_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4225_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4225_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec(v_numDigits_4212_);
lean_dec_ref(v_candidates_4211_);
v_a_4249_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4213_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4213_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
v_a_4257_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4209_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4209_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4265_, lean_object* v_candidates_x3f_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4265_, v_candidates_x3f_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec(v_a_4267_);
lean_dec_ref(v_c_4265_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4279_, uint64_t v_a_4280_, lean_object* v_c_4281_, lean_object* v_numDigits_4282_, lean_object* v_as_4283_, size_t v_sz_4284_, size_t v_i_4285_, lean_object* v_b_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4279_, v_a_4280_, v_c_4281_, v_numDigits_4282_, v_as_4283_, v_sz_4284_, v_i_4285_, v_b_4286_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4299_ = _args[0];
lean_object* v_a_4300_ = _args[1];
lean_object* v_c_4301_ = _args[2];
lean_object* v_numDigits_4302_ = _args[3];
lean_object* v_as_4303_ = _args[4];
lean_object* v_sz_4304_ = _args[5];
lean_object* v_i_4305_ = _args[6];
lean_object* v_b_4306_ = _args[7];
lean_object* v___y_4307_ = _args[8];
lean_object* v___y_4308_ = _args[9];
lean_object* v___y_4309_ = _args[10];
lean_object* v___y_4310_ = _args[11];
lean_object* v___y_4311_ = _args[12];
lean_object* v___y_4312_ = _args[13];
lean_object* v___y_4313_ = _args[14];
lean_object* v___y_4314_ = _args[15];
lean_object* v___y_4315_ = _args[16];
lean_object* v___y_4316_ = _args[17];
lean_object* v___y_4317_ = _args[18];
_start:
{
uint64_t v___x_7894__boxed_4318_; uint64_t v_a_7895__boxed_4319_; size_t v_sz_boxed_4320_; size_t v_i_boxed_4321_; lean_object* v_res_4322_; 
v___x_7894__boxed_4318_ = lean_unbox_uint64(v___x_4299_);
lean_dec_ref(v___x_4299_);
v_a_7895__boxed_4319_ = lean_unbox_uint64(v_a_4300_);
lean_dec_ref(v_a_4300_);
v_sz_boxed_4320_ = lean_unbox_usize(v_sz_4304_);
lean_dec(v_sz_4304_);
v_i_boxed_4321_ = lean_unbox_usize(v_i_4305_);
lean_dec(v_i_4305_);
v_res_4322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7894__boxed_4318_, v_a_7895__boxed_4319_, v_c_4301_, v_numDigits_4302_, v_as_4303_, v_sz_boxed_4320_, v_i_boxed_4321_, v_b_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v_as_4303_);
lean_dec_ref(v_c_4301_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_numDigits_4350_; uint64_t v_anchor_4351_; lean_object* v_ordinal_4352_; lean_object* v___x_4353_; 
v_numDigits_4350_ = lean_ctor_get(v_info_4347_, 0);
v_anchor_4351_ = lean_ctor_get_uint64(v_info_4347_, sizeof(void*)*2);
v_ordinal_4352_ = lean_ctor_get(v_info_4347_, 1);
v___x_4353_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4350_, v_anchor_4351_, v_a_4348_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4390_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4356_ = v___x_4353_;
v_isShared_4357_ = v_isSharedCheck_4390_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4390_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4358_ = lean_unsigned_to_nat(0u);
v___x_4359_ = lean_nat_dec_eq(v_ordinal_4352_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v_ref_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4376_; 
v_ref_4360_ = lean_ctor_get(v_a_4348_, 2);
v___x_4361_ = l_Lean_SourceInfo_fromRef(v_ref_4360_, v___x_4359_);
v___x_4362_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4363_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4361_, 3);
v___x_4364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4361_);
lean_ctor_set(v___x_4364_, 1, v___x_4362_);
v___x_4365_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4366_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4361_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = lean_unsigned_to_nat(1u);
v___x_4369_ = lean_nat_add(v_ordinal_4352_, v___x_4368_);
v___x_4370_ = l_Nat_reprFast(v___x_4369_);
v___x_4371_ = lean_box(2);
v___x_4372_ = l_Lean_Syntax_mkNumLit(v___x_4370_, v___x_4371_);
v___x_4373_ = l_Lean_Syntax_node3(v___x_4361_, v___x_4365_, v_a_4354_, v___x_4367_, v___x_4372_);
v___x_4374_ = l_Lean_Syntax_node2(v___x_4361_, v___x_4363_, v___x_4364_, v___x_4373_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4374_);
v___x_4376_ = v___x_4356_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
else
{
lean_object* v_ref_4378_; uint8_t v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
v_ref_4378_ = lean_ctor_get(v_a_4348_, 2);
v___x_4379_ = 0;
v___x_4380_ = l_Lean_SourceInfo_fromRef(v_ref_4378_, v___x_4379_);
v___x_4381_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4382_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4380_, 2);
v___x_4383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4380_);
lean_ctor_set(v___x_4383_, 1, v___x_4381_);
v___x_4384_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4385_ = l_Lean_Syntax_node1(v___x_4380_, v___x_4384_, v_a_4354_);
v___x_4386_ = l_Lean_Syntax_node2(v___x_4380_, v___x_4382_, v___x_4383_, v___x_4385_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4386_);
v___x_4388_ = v___x_4356_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
return v___x_4353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4391_, v_a_4392_);
lean_dec_ref(v_a_4392_);
lean_dec_ref(v_info_4391_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4395_, v_a_4396_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4400_, v_a_4401_, v_a_4402_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec_ref(v_info_4400_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v_p_4436_; lean_object* v___x_4439_; 
lean_inc_ref(v_proof_4417_);
v___x_4439_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4417_, v_a_4419_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4466_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4442_ = v___x_4439_;
v_isShared_4443_ = v_isSharedCheck_4466_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4439_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4466_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4444_; uint8_t v___x_4445_; 
v___x_4444_ = l_Lean_Expr_cleanupAnnotations(v_a_4440_);
lean_dec(v_a_4440_);
v___x_4445_ = l_Lean_Expr_isApp(v___x_4444_);
if (v___x_4445_ == 0)
{
lean_dec_ref(v___x_4444_);
lean_del_object(v___x_4442_);
v___y_4424_ = v_a_4418_;
v___y_4425_ = v_a_4419_;
v___y_4426_ = v_a_4420_;
v___y_4427_ = v_a_4421_;
goto v___jp_4423_;
}
else
{
lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4444_);
v___x_4447_ = l_Lean_Expr_isApp(v___x_4446_);
if (v___x_4447_ == 0)
{
lean_dec_ref(v___x_4446_);
lean_dec_ref(v___x_4444_);
lean_del_object(v___x_4442_);
v___y_4424_ = v_a_4418_;
v___y_4425_ = v_a_4419_;
v___y_4426_ = v_a_4420_;
v___y_4427_ = v_a_4421_;
goto v___jp_4423_;
}
else
{
lean_object* v_arg_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; uint8_t v___x_4451_; 
v_arg_4448_ = lean_ctor_get(v___x_4444_, 1);
lean_inc_ref(v_arg_4448_);
lean_dec_ref(v___x_4444_);
v___x_4449_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4446_);
v___x_4450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4451_ = l_Lean_Expr_isConstOf(v___x_4449_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; uint8_t v___x_4453_; 
lean_dec_ref(v___x_4446_);
lean_del_object(v___x_4442_);
v___x_4452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4453_ = l_Lean_Expr_isConstOf(v___x_4449_, v___x_4452_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; uint8_t v___x_4455_; 
v___x_4454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4455_ = l_Lean_Expr_isConstOf(v___x_4449_, v___x_4454_);
lean_dec_ref(v___x_4449_);
if (v___x_4455_ == 0)
{
lean_dec_ref(v_arg_4448_);
v___y_4424_ = v_a_4418_;
v___y_4425_ = v_a_4419_;
v___y_4426_ = v_a_4420_;
v___y_4427_ = v_a_4421_;
goto v___jp_4423_;
}
else
{
lean_dec_ref(v_proof_4417_);
v_p_4436_ = v_arg_4448_;
goto v___jp_4435_;
}
}
else
{
lean_dec_ref(v___x_4449_);
lean_dec_ref(v_proof_4417_);
v_p_4436_ = v_arg_4448_;
goto v___jp_4435_;
}
}
else
{
lean_object* v_arg_4456_; uint8_t v___x_4457_; 
lean_dec_ref(v___x_4449_);
lean_dec_ref(v_proof_4417_);
v_arg_4456_ = lean_ctor_get(v___x_4446_, 1);
lean_inc_ref(v_arg_4456_);
lean_dec_ref(v___x_4446_);
v___x_4457_ = l_Lean_Expr_isFalse(v_arg_4456_);
lean_dec_ref(v_arg_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4460_; 
lean_dec_ref(v_arg_4448_);
v___x_4458_ = lean_box(0);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4458_);
v___x_4460_ = v___x_4442_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4458_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4462_, 0, v_arg_4448_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4462_);
v___x_4464_ = v___x_4442_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec_ref(v_proof_4417_);
v_a_4467_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4439_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4439_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
v___jp_4423_:
{
if (lean_obj_tag(v_proof_4417_) == 6)
{
lean_object* v_body_4428_; uint8_t v___x_4429_; 
v_body_4428_ = lean_ctor_get(v_proof_4417_, 2);
lean_inc_ref(v_body_4428_);
lean_dec_ref_known(v_proof_4417_, 3);
v___x_4429_ = l_Lean_Expr_hasLooseBVars(v_body_4428_);
if (v___x_4429_ == 0)
{
v_proof_4417_ = v_body_4428_;
v_a_4418_ = v___y_4424_;
v_a_4419_ = v___y_4425_;
v_a_4420_ = v___y_4426_;
v_a_4421_ = v___y_4427_;
goto _start;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
lean_dec_ref(v_body_4428_);
v___x_4431_ = lean_box(0);
v___x_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
}
else
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
lean_dec_ref(v_proof_4417_);
v___x_4433_ = lean_box(0);
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
return v___x_4434_;
}
}
v___jp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4437_, 0, v_p_4436_);
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
return v___x_4438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v___x_4485_; 
v___x_4485_ = l_Lean_Expr_hasMVar(v_e_4482_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4486_, 0, v_e_4482_);
return v___x_4486_;
}
else
{
lean_object* v___x_4487_; lean_object* v_mctx_4488_; lean_object* v___x_4489_; lean_object* v_fst_4490_; lean_object* v_snd_4491_; lean_object* v___x_4492_; lean_object* v_cache_4493_; lean_object* v_zetaDeltaFVarIds_4494_; lean_object* v_postponed_4495_; lean_object* v_diag_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4505_; 
v___x_4487_ = lean_st_ref_get(v___y_4483_);
v_mctx_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc_ref(v_mctx_4488_);
lean_dec(v___x_4487_);
v___x_4489_ = l_Lean_instantiateMVarsCore(v_mctx_4488_, v_e_4482_);
v_fst_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_fst_4490_);
v_snd_4491_ = lean_ctor_get(v___x_4489_, 1);
lean_inc(v_snd_4491_);
lean_dec_ref(v___x_4489_);
v___x_4492_ = lean_st_ref_take(v___y_4483_);
v_cache_4493_ = lean_ctor_get(v___x_4492_, 1);
v_zetaDeltaFVarIds_4494_ = lean_ctor_get(v___x_4492_, 2);
v_postponed_4495_ = lean_ctor_get(v___x_4492_, 3);
v_diag_4496_ = lean_ctor_get(v___x_4492_, 4);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4505_ == 0)
{
lean_object* v_unused_4506_; 
v_unused_4506_ = lean_ctor_get(v___x_4492_, 0);
lean_dec(v_unused_4506_);
v___x_4498_ = v___x_4492_;
v_isShared_4499_ = v_isSharedCheck_4505_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_diag_4496_);
lean_inc(v_postponed_4495_);
lean_inc(v_zetaDeltaFVarIds_4494_);
lean_inc(v_cache_4493_);
lean_dec(v___x_4492_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4505_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 0, v_snd_4491_);
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_snd_4491_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_cache_4493_);
lean_ctor_set(v_reuseFailAlloc_4504_, 2, v_zetaDeltaFVarIds_4494_);
lean_ctor_set(v_reuseFailAlloc_4504_, 3, v_postponed_4495_);
lean_ctor_set(v_reuseFailAlloc_4504_, 4, v_diag_4496_);
v___x_4501_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_st_ref_put(v___y_4483_, v___x_4501_);
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v_fst_4490_);
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4507_, v___y_4508_);
lean_dec(v___y_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4511_, v___y_4513_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4525_, lean_object* v_x_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4525_, v_x_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
v_a_4541_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4532_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4532_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4549_, lean_object* v_x_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4549_, v_x_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4557_, lean_object* v_mvarId_4558_, lean_object* v_x_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4558_, v_x_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4566_, lean_object* v_mvarId_4567_, lean_object* v_x_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4566_, v_mvarId_4567_, v_x_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4592_; 
v___x_4581_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4575_, v___y_4577_);
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4592_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4592_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
uint8_t v___x_4586_; 
v___x_4586_ = l_Lean_Expr_hasSyntheticSorry(v_a_4582_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; 
lean_del_object(v___x_4584_);
v___x_4587_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4582_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
return v___x_4587_;
}
else
{
lean_object* v___x_4588_; lean_object* v___x_4590_; 
lean_dec(v_a_4582_);
v___x_4588_ = lean_box(0);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4588_);
v___x_4590_ = v___x_4584_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4588_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; lean_object* v___f_4607_; lean_object* v___x_4608_; 
lean_inc(v_mvarId_4600_);
v___x_4606_ = l_Lean_mkMVar(v_mvarId_4600_);
v___f_4607_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4607_, 0, v___x_4606_);
v___x_4608_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4600_, v___f_4607_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
return v_res_4615_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4637_){
_start:
{
if (lean_obj_tag(v_x_4637_) == 0)
{
uint8_t v___x_4638_; 
v___x_4638_ = 1;
return v___x_4638_;
}
else
{
lean_object* v_head_4639_; lean_object* v_tail_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v_head_4639_ = lean_ctor_get(v_x_4637_, 0);
lean_inc_n(v_head_4639_, 2);
v_tail_4640_ = lean_ctor_get(v_x_4637_, 1);
lean_inc(v_tail_4640_);
lean_dec_ref_known(v_x_4637_, 2);
v___x_4641_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4642_ = l_Lean_Syntax_isOfKind(v_head_4639_, v___x_4641_);
if (v___x_4642_ == 0)
{
lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4643_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4639_);
v___x_4644_ = l_Lean_Syntax_isOfKind(v_head_4639_, v___x_4643_);
if (v___x_4644_ == 0)
{
lean_dec(v_head_4639_);
v_x_4637_ = v_tail_4640_;
goto _start;
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v___x_4646_ = lean_unsigned_to_nat(1u);
v___x_4647_ = l_Lean_Syntax_getArg(v_head_4639_, v___x_4646_);
lean_dec(v_head_4639_);
v___x_4648_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4649_ = l_Lean_Syntax_isOfKind(v___x_4647_, v___x_4648_);
if (v___x_4649_ == 0)
{
v_x_4637_ = v_tail_4640_;
goto _start;
}
else
{
lean_dec(v_tail_4640_);
return v___x_4642_;
}
}
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4651_ = lean_unsigned_to_nat(3u);
v___x_4652_ = l_Lean_Syntax_getArg(v_head_4639_, v___x_4651_);
lean_dec(v_head_4639_);
v___x_4653_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4654_ = l_Lean_Syntax_isOfKind(v___x_4652_, v___x_4653_);
if (v___x_4654_ == 0)
{
v_x_4637_ = v_tail_4640_;
goto _start;
}
else
{
uint8_t v___x_4656_; 
lean_dec(v_tail_4640_);
v___x_4656_ = 0;
return v___x_4656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4657_){
_start:
{
uint8_t v_res_4658_; lean_object* v_r_4659_; 
v_res_4658_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4657_);
v_r_4659_ = lean_box(v_res_4658_);
return v_r_4659_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4660_){
_start:
{
uint8_t v___x_4661_; 
v___x_4661_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4662_){
_start:
{
uint8_t v_res_4663_; lean_object* v_r_4664_; 
v_res_4663_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4662_);
v_r_4664_ = lean_box(v_res_4663_);
return v_r_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4680_, lean_object* v_a_4681_){
_start:
{
if (lean_obj_tag(v_seq_4680_) == 0)
{
lean_object* v_ref_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v_ref_4683_ = lean_ctor_get(v_a_4681_, 2);
v___x_4684_ = 0;
v___x_4685_ = l_Lean_SourceInfo_fromRef(v_ref_4683_, v___x_4684_);
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4685_);
v___x_4688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4685_);
lean_ctor_set(v___x_4688_, 1, v___x_4686_);
v___x_4689_ = l_Lean_Syntax_node1(v___x_4685_, v___x_4687_, v___x_4688_);
v___x_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
return v___x_4690_;
}
else
{
lean_object* v_tail_4691_; 
v_tail_4691_ = lean_ctor_get(v_seq_4680_, 1);
if (lean_obj_tag(v_tail_4691_) == 0)
{
lean_object* v_head_4692_; lean_object* v___x_4693_; 
v_head_4692_ = lean_ctor_get(v_seq_4680_, 0);
lean_inc(v_head_4692_);
lean_dec_ref_known(v_seq_4680_, 2);
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v_head_4692_);
return v___x_4693_;
}
else
{
lean_object* v_head_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4716_; 
lean_inc(v_tail_4691_);
v_head_4694_ = lean_ctor_get(v_seq_4680_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v_seq_4680_);
if (v_isSharedCheck_4716_ == 0)
{
lean_object* v_unused_4717_; 
v_unused_4717_ = lean_ctor_get(v_seq_4680_, 1);
lean_dec(v_unused_4717_);
v___x_4696_ = v_seq_4680_;
v_isShared_4697_ = v_isSharedCheck_4716_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_head_4694_);
lean_dec(v_seq_4680_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4716_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4715_; 
v___x_4698_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4691_, v_a_4681_);
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4715_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4715_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v_ref_4703_; uint8_t v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4709_; 
v_ref_4703_ = lean_ctor_get(v_a_4681_, 2);
v___x_4704_ = 0;
v___x_4705_ = l_Lean_SourceInfo_fromRef(v_ref_4703_, v___x_4704_);
v___x_4706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4705_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set_tag(v___x_4696_, 2);
lean_ctor_set(v___x_4696_, 1, v___x_4707_);
lean_ctor_set(v___x_4696_, 0, v___x_4705_);
v___x_4709_ = v___x_4696_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4707_);
v___x_4709_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4710_; lean_object* v___x_4712_; 
v___x_4710_ = l_Lean_Syntax_node3(v___x_4705_, v___x_4706_, v_head_4694_, v___x_4709_, v_a_4699_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4710_);
v___x_4712_ = v___x_4701_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4718_, v_a_4719_);
lean_dec_ref(v_a_4719_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4722_, v_a_4723_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4732_, lean_object* v_seq_4733_, lean_object* v_a_4734_){
_start:
{
if (lean_obj_tag(v_seq_4733_) == 0)
{
lean_object* v___x_4736_; 
v___x_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4736_, 0, v_cases_4732_);
return v___x_4736_;
}
else
{
lean_object* v___x_4737_; lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4752_; 
v___x_4737_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4733_, v_a_4734_);
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4740_ = v___x_4737_;
v_isShared_4741_ = v_isSharedCheck_4752_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4752_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v_ref_4742_; uint8_t v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4750_; 
v_ref_4742_ = lean_ctor_get(v_a_4734_, 2);
v___x_4743_ = 0;
v___x_4744_ = l_Lean_SourceInfo_fromRef(v_ref_4742_, v___x_4743_);
v___x_4745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4744_);
v___x_4747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4744_);
lean_ctor_set(v___x_4747_, 1, v___x_4746_);
v___x_4748_ = l_Lean_Syntax_node3(v___x_4744_, v___x_4745_, v_cases_4732_, v___x_4747_, v_a_4738_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v___x_4748_);
v___x_4750_ = v___x_4740_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4753_, lean_object* v_seq_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4753_, v_seq_4754_, v_a_4755_);
lean_dec_ref(v_a_4755_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4758_, lean_object* v_seq_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4758_, v_seq_4759_, v_a_4760_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4764_, lean_object* v_seq_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4764_, v_seq_4765_, v_a_4766_, v_a_4767_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4769_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4770_, lean_object* v_x_4771_){
_start:
{
if (lean_obj_tag(v_x_4770_) == 0)
{
if (lean_obj_tag(v_x_4771_) == 0)
{
uint8_t v___x_4772_; 
v___x_4772_ = 1;
return v___x_4772_;
}
else
{
uint8_t v___x_4773_; 
v___x_4773_ = 0;
return v___x_4773_;
}
}
else
{
if (lean_obj_tag(v_x_4771_) == 0)
{
uint8_t v___x_4774_; 
v___x_4774_ = 0;
return v___x_4774_;
}
else
{
lean_object* v_head_4775_; lean_object* v_tail_4776_; lean_object* v_head_4777_; lean_object* v_tail_4778_; uint8_t v___x_4779_; 
v_head_4775_ = lean_ctor_get(v_x_4770_, 0);
v_tail_4776_ = lean_ctor_get(v_x_4770_, 1);
v_head_4777_ = lean_ctor_get(v_x_4771_, 0);
v_tail_4778_ = lean_ctor_get(v_x_4771_, 1);
v___x_4779_ = l_Lean_Syntax_structEq(v_head_4775_, v_head_4777_);
if (v___x_4779_ == 0)
{
return v___x_4779_;
}
else
{
v_x_4770_ = v_tail_4776_;
v_x_4771_ = v_tail_4778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4781_, lean_object* v_x_4782_){
_start:
{
uint8_t v_res_4783_; lean_object* v_r_4784_; 
v_res_4783_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4781_, v_x_4782_);
lean_dec(v_x_4782_);
lean_dec(v_x_4781_);
v_r_4784_ = lean_box(v_res_4783_);
return v_r_4784_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4785_, lean_object* v___x_4786_, lean_object* v_as_4787_, size_t v_i_4788_, size_t v_stop_4789_){
_start:
{
uint8_t v___x_4794_; 
v___x_4794_ = lean_usize_dec_eq(v_i_4788_, v_stop_4789_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; uint8_t v___x_4796_; 
v___x_4795_ = lean_array_uget_borrowed(v_as_4787_, v_i_4788_);
v___x_4796_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4795_, v_alt_4785_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; uint8_t v___x_4798_; 
v___x_4797_ = lean_unsigned_to_nat(0u);
v___x_4798_ = lean_nat_dec_lt(v___x_4797_, v___x_4786_);
if (v___x_4798_ == 0)
{
goto v___jp_4790_;
}
else
{
return v___x_4798_;
}
}
else
{
goto v___jp_4790_;
}
}
else
{
uint8_t v___x_4799_; 
v___x_4799_ = 0;
return v___x_4799_;
}
v___jp_4790_:
{
size_t v___x_4791_; size_t v___x_4792_; 
v___x_4791_ = ((size_t)1ULL);
v___x_4792_ = lean_usize_add(v_i_4788_, v___x_4791_);
v_i_4788_ = v___x_4792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4800_, lean_object* v___x_4801_, lean_object* v_as_4802_, lean_object* v_i_4803_, lean_object* v_stop_4804_){
_start:
{
size_t v_i_boxed_4805_; size_t v_stop_boxed_4806_; uint8_t v_res_4807_; lean_object* v_r_4808_; 
v_i_boxed_4805_ = lean_unbox_usize(v_i_4803_);
lean_dec(v_i_4803_);
v_stop_boxed_4806_ = lean_unbox_usize(v_stop_4804_);
lean_dec(v_stop_4804_);
v_res_4807_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4800_, v___x_4801_, v_as_4802_, v_i_boxed_4805_, v_stop_boxed_4806_);
lean_dec_ref(v_as_4802_);
lean_dec(v___x_4801_);
lean_dec(v_alt_4800_);
v_r_4808_ = lean_box(v_res_4807_);
return v_r_4808_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4809_){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; 
v___x_4810_ = lean_unsigned_to_nat(0u);
v___x_4811_ = lean_array_get_size(v_alts_4809_);
v___x_4812_ = lean_nat_dec_lt(v___x_4810_, v___x_4811_);
if (v___x_4812_ == 0)
{
uint8_t v___x_4813_; 
v___x_4813_ = 1;
return v___x_4813_;
}
else
{
lean_object* v_alt_4814_; uint8_t v___x_4815_; 
v_alt_4814_ = lean_array_fget_borrowed(v_alts_4809_, v___x_4810_);
lean_inc(v_alt_4814_);
v___x_4815_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4814_);
if (v___x_4815_ == 0)
{
return v___x_4815_;
}
else
{
if (v___x_4812_ == 0)
{
return v___x_4812_;
}
else
{
size_t v___x_4816_; size_t v___x_4817_; uint8_t v___x_4818_; 
v___x_4816_ = ((size_t)0ULL);
v___x_4817_ = lean_usize_of_nat(v___x_4811_);
v___x_4818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4814_, v___x_4811_, v_alts_4809_, v___x_4816_, v___x_4817_);
if (v___x_4818_ == 0)
{
return v___x_4812_;
}
else
{
uint8_t v___x_4819_; 
v___x_4819_ = 0;
return v___x_4819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4820_){
_start:
{
uint8_t v_res_4821_; lean_object* v_r_4822_; 
v_res_4821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4820_);
lean_dec_ref(v_alts_4820_);
v_r_4822_ = lean_box(v_res_4821_);
return v_r_4822_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4830_){
_start:
{
if (lean_obj_tag(v_alt_4830_) == 1)
{
lean_object* v_tail_4831_; 
v_tail_4831_ = lean_ctor_get(v_alt_4830_, 1);
if (lean_obj_tag(v_tail_4831_) == 0)
{
lean_object* v_head_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v_head_4832_ = lean_ctor_get(v_alt_4830_, 0);
lean_inc(v_head_4832_);
lean_dec_ref_known(v_alt_4830_, 2);
v___x_4833_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4834_ = l_Lean_Syntax_isOfKind(v_head_4832_, v___x_4833_);
return v___x_4834_;
}
else
{
uint8_t v___x_4835_; 
lean_dec_ref_known(v_alt_4830_, 2);
v___x_4835_ = 0;
return v___x_4835_;
}
}
else
{
uint8_t v___x_4836_; 
lean_dec(v_alt_4830_);
v___x_4836_ = 0;
return v___x_4836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4837_){
_start:
{
uint8_t v_res_4838_; lean_object* v_r_4839_; 
v_res_4838_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4837_);
v_r_4839_ = lean_box(v_res_4838_);
return v_r_4839_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4840_, lean_object* v_x_4841_, lean_object* v___y_4842_){
_start:
{
if (lean_obj_tag(v_x_4840_) == 0)
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = l_List_reverse___redArg(v_x_4841_);
v___x_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
return v___x_4845_;
}
else
{
lean_object* v_head_4846_; lean_object* v_tail_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4865_; 
v_head_4846_ = lean_ctor_get(v_x_4840_, 0);
v_tail_4847_ = lean_ctor_get(v_x_4840_, 1);
v_isSharedCheck_4865_ = !lean_is_exclusive(v_x_4840_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4849_ = v_x_4840_;
v_isShared_4850_ = v_isSharedCheck_4865_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_tail_4847_);
lean_inc(v_head_4846_);
lean_dec(v_x_4840_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4865_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4846_, v___y_4842_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v_x_4841_);
lean_ctor_set(v___x_4849_, 0, v_a_4852_);
v___x_4854_ = v___x_4849_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4852_);
lean_ctor_set(v_reuseFailAlloc_4856_, 1, v_x_4841_);
v___x_4854_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
v_x_4840_ = v_tail_4847_;
v_x_4841_ = v___x_4854_;
goto _start;
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_del_object(v___x_4849_);
lean_dec(v_tail_4847_);
lean_dec(v_x_4841_);
v_a_4857_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4851_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4851_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4866_, lean_object* v_x_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4866_, v_x_4867_, v___y_4868_);
lean_dec_ref(v___y_4868_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4871_, lean_object* v_alts_4872_, uint8_t v_compress_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v_seq_4878_; 
if (v_compress_4873_ == 0)
{
goto v___jp_4881_;
}
else
{
uint8_t v___x_4891_; 
v___x_4891_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4872_);
if (v___x_4891_ == 0)
{
goto v___jp_4881_;
}
else
{
lean_object* v___x_4892_; lean_object* v___x_4893_; uint8_t v___x_4894_; 
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = lean_array_get_size(v_alts_4872_);
v___x_4894_ = lean_nat_dec_lt(v___x_4892_, v___x_4893_);
if (v___x_4894_ == 0)
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
lean_dec_ref(v_alts_4872_);
v___x_4895_ = lean_box(0);
v___x_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4896_, 0, v_cases_4871_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
v___x_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
return v___x_4897_;
}
else
{
lean_object* v___x_4898_; lean_object* v_firstAlt_4899_; uint8_t v___x_4900_; 
v___x_4898_ = lean_box(0);
v_firstAlt_4899_ = lean_array_get(v___x_4898_, v_alts_4872_, v___x_4892_);
lean_dec_ref(v_alts_4872_);
lean_inc(v_firstAlt_4899_);
v___x_4900_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4899_);
if (v___x_4900_ == 0)
{
lean_object* v___x_4901_; lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4910_; 
v___x_4901_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4871_, v_firstAlt_4899_, v_a_4874_);
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4904_ = v___x_4901_;
v_isShared_4905_ = v_isSharedCheck_4910_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4910_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4906_; lean_object* v___x_4908_; 
v___x_4906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4906_, 0, v_a_4902_);
lean_ctor_set(v___x_4906_, 1, v___x_4898_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v___x_4906_);
v___x_4908_ = v___x_4904_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4906_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
else
{
lean_object* v___x_4911_; 
lean_dec(v_cases_4871_);
v___x_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4911_, 0, v_firstAlt_4899_);
return v___x_4911_;
}
}
}
}
v___jp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4879_, 0, v_cases_4871_);
lean_ctor_set(v___x_4879_, 1, v_seq_4878_);
v___x_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4879_);
return v___x_4880_;
}
v___jp_4881_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4882_ = lean_array_get_size(v_alts_4872_);
v___x_4883_ = lean_unsigned_to_nat(1u);
v___x_4884_ = lean_nat_dec_eq(v___x_4882_, v___x_4883_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_array_to_list(v_alts_4872_);
v___x_4886_ = lean_box(0);
v___x_4887_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4885_, v___x_4886_, v_a_4874_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
v_seq_4878_ = v_a_4888_;
goto v___jp_4877_;
}
else
{
lean_dec(v_cases_4871_);
return v___x_4887_;
}
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_unsigned_to_nat(0u);
v___x_4890_ = lean_array_fget(v_alts_4872_, v___x_4889_);
lean_dec_ref(v_alts_4872_);
v_seq_4878_ = v___x_4890_;
goto v___jp_4877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4912_, lean_object* v_alts_4913_, lean_object* v_compress_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
uint8_t v_compress_boxed_4918_; lean_object* v_res_4919_; 
v_compress_boxed_4918_ = lean_unbox(v_compress_4914_);
v_res_4919_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4912_, v_alts_4913_, v_compress_boxed_4918_, v_a_4915_, v_a_4916_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4920_, lean_object* v_x_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4920_, v_x_4921_, v___y_4922_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4926_, lean_object* v_x_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4926_, v_x_4927_, v___y_4928_, v___y_4929_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4935_; lean_object* v_env_4936_; uint8_t v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4935_ = lean_st_ref_get(v___y_4933_);
v_env_4936_ = lean_ctor_get(v___x_4935_, 0);
lean_inc_ref(v_env_4936_);
lean_dec(v___x_4935_);
v___x_4937_ = l_Lean_Meta_isMatcherAppCore(v_env_4936_, v_e_4932_);
v___x_4938_ = lean_box(v___x_4937_);
v___x_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4938_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v_e_4940_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4944_, v___y_4954_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec_ref(v_e_4957_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v___x_4981_; 
lean_inc(v___y_4975_);
lean_inc_ref(v___y_4974_);
lean_inc(v___y_4973_);
lean_inc_ref(v___y_4972_);
lean_inc(v___y_4971_);
v___x_4981_ = lean_apply_10(v_x_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, lean_box(0));
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
lean_dec(v___y_4987_);
lean_dec_ref(v___y_4986_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec(v___y_4983_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4994_, lean_object* v_x_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v___f_5006_; lean_object* v___x_5007_; 
lean_inc(v___y_5000_);
lean_inc_ref(v___y_4999_);
lean_inc(v___y_4998_);
lean_inc_ref(v___y_4997_);
lean_inc(v___y_4996_);
v___f_5006_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5006_, 0, v_x_4995_);
lean_closure_set(v___f_5006_, 1, v___y_4996_);
lean_closure_set(v___f_5006_, 2, v___y_4997_);
lean_closure_set(v___f_5006_, 3, v___y_4998_);
lean_closure_set(v___f_5006_, 4, v___y_4999_);
lean_closure_set(v___f_5006_, 5, v___y_5000_);
v___x_5007_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4994_, v___f_5006_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
if (lean_obj_tag(v___x_5007_) == 0)
{
return v___x_5007_;
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_5007_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_5007_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5016_, lean_object* v_x_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5016_, v_x_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5029_, lean_object* v_mvarId_5030_, lean_object* v_x_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5030_, v_x_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5043_, lean_object* v_mvarId_5044_, lean_object* v_x_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5043_, v_mvarId_5044_, v_x_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v___y_5046_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_e_5057_, lean_object* v___y_5058_){
_start:
{
uint8_t v___x_5060_; 
v___x_5060_ = l_Lean_Expr_hasMVar(v_e_5057_);
if (v___x_5060_ == 0)
{
lean_object* v___x_5061_; 
v___x_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5061_, 0, v_e_5057_);
return v___x_5061_;
}
else
{
lean_object* v___x_5062_; lean_object* v_mctx_5063_; lean_object* v___x_5064_; lean_object* v_fst_5065_; lean_object* v_snd_5066_; lean_object* v___x_5067_; lean_object* v_cache_5068_; lean_object* v_zetaDeltaFVarIds_5069_; lean_object* v_postponed_5070_; lean_object* v_diag_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5080_; 
v___x_5062_ = lean_st_ref_get(v___y_5058_);
v_mctx_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc_ref(v_mctx_5063_);
lean_dec(v___x_5062_);
v___x_5064_ = l_Lean_instantiateMVarsCore(v_mctx_5063_, v_e_5057_);
v_fst_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_fst_5065_);
v_snd_5066_ = lean_ctor_get(v___x_5064_, 1);
lean_inc(v_snd_5066_);
lean_dec_ref(v___x_5064_);
v___x_5067_ = lean_st_ref_take(v___y_5058_);
v_cache_5068_ = lean_ctor_get(v___x_5067_, 1);
v_zetaDeltaFVarIds_5069_ = lean_ctor_get(v___x_5067_, 2);
v_postponed_5070_ = lean_ctor_get(v___x_5067_, 3);
v_diag_5071_ = lean_ctor_get(v___x_5067_, 4);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5080_ == 0)
{
lean_object* v_unused_5081_; 
v_unused_5081_ = lean_ctor_get(v___x_5067_, 0);
lean_dec(v_unused_5081_);
v___x_5073_ = v___x_5067_;
v_isShared_5074_ = v_isSharedCheck_5080_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_diag_5071_);
lean_inc(v_postponed_5070_);
lean_inc(v_zetaDeltaFVarIds_5069_);
lean_inc(v_cache_5068_);
lean_dec(v___x_5067_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5080_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v_snd_5066_);
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_snd_5066_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v_cache_5068_);
lean_ctor_set(v_reuseFailAlloc_5079_, 2, v_zetaDeltaFVarIds_5069_);
lean_ctor_set(v_reuseFailAlloc_5079_, 3, v_postponed_5070_);
lean_ctor_set(v_reuseFailAlloc_5079_, 4, v_diag_5071_);
v___x_5076_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5077_ = lean_st_ref_put(v___y_5058_, v___x_5076_);
v___x_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5078_, 0, v_fst_5065_);
return v___x_5078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_e_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_e_5082_, v___y_5083_);
lean_dec(v___y_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_e_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_e_5086_, v___y_5093_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_e_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_e_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
lean_dec(v___y_5099_);
return v_res_5109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5111_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5112_ = l_Lean_stringToMessageData(v___x_5111_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5113_, lean_object* v_c_5114_, lean_object* v_a_5115_, lean_object* v_numCases_5116_, uint8_t v_isRec_5117_, lean_object* v_anchorInfo_x3f_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_){
_start:
{
lean_object* v_mvarIds_5131_; lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5113_, v___y_5119_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; lean_object* v___y_5184_; lean_object* v___x_5236_; uint8_t v___x_5239_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___x_5181_, 1);
v___x_5236_ = lean_unsigned_to_nat(1u);
v___x_5239_ = lean_nat_dec_lt(v___x_5236_, v_numCases_5116_);
if (v___x_5239_ == 0)
{
if (v_isRec_5117_ == 0)
{
lean_inc(v_a_5182_);
v___y_5184_ = v_a_5182_;
goto v___jp_5183_;
}
else
{
goto v___jp_5237_;
}
}
else
{
goto v___jp_5237_;
}
v___jp_5183_:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5114_);
lean_inc_ref(v___x_5113_);
v___x_5186_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5113_, v___y_5184_, v_numCases_5116_, v___x_5185_, v___y_5122_, v___y_5125_, v___y_5127_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v___x_5187_; 
lean_dec_ref_known(v___x_5186_, 1);
lean_inc_ref(v___x_5113_);
v___x_5187_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5113_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_toCold_5188_; lean_object* v_options_5189_; uint8_t v_hasTrace_5190_; 
lean_dec_ref_known(v___x_5187_, 1);
v_toCold_5188_ = lean_ctor_get(v___y_5127_, 0);
v_options_5189_ = lean_ctor_get(v_toCold_5188_, 2);
v_hasTrace_5190_ = lean_ctor_get_uint8(v_options_5189_, sizeof(void*)*1);
if (v_hasTrace_5190_ == 0)
{
lean_dec(v_a_5182_);
goto v___jp_5134_;
}
else
{
lean_object* v_inheritedTraceOptions_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; 
v_inheritedTraceOptions_5191_ = lean_ctor_get(v_toCold_5188_, 11);
v___x_5192_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5193_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5191_, v_options_5189_, v___x_5193_);
if (v___x_5194_ == 0)
{
lean_dec(v_a_5182_);
goto v___jp_5134_;
}
else
{
lean_object* v___x_5195_; 
v___x_5195_ = l_Lean_Meta_Grind_updateLastTag(v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; 
lean_dec_ref_known(v___x_5195_, 1);
lean_inc_ref(v___x_5113_);
v___x_5196_ = l_Lean_MessageData_ofExpr(v___x_5113_);
v___x_5197_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5196_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
v___x_5199_ = l_Nat_reprFast(v_a_5182_);
v___x_5200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
v___x_5201_ = l_Lean_MessageData_ofFormat(v___x_5200_);
v___x_5202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5198_);
lean_ctor_set(v___x_5202_, 1, v___x_5201_);
v___x_5203_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5192_, v___x_5202_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_dec_ref_known(v___x_5203_, 1);
goto v___jp_5134_;
}
else
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5211_; 
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5211_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5211_ == 0)
{
v___x_5206_ = v___x_5203_;
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5203_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5209_; 
if (v_isShared_5207_ == 0)
{
v___x_5209_ = v___x_5206_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_a_5204_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
lean_dec(v_a_5182_);
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5212_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5195_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5195_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
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
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_dec(v_a_5182_);
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5220_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5187_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5187_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_dec(v_a_5182_);
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5228_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5186_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5186_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
v___jp_5237_:
{
lean_object* v___x_5238_; 
v___x_5238_ = lean_nat_add(v_a_5182_, v___x_5236_);
v___y_5184_ = v___x_5238_;
goto v___jp_5183_;
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_numCases_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5240_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5242_ = v___x_5181_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5181_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
v___jp_5130_:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5132_, 0, v_mvarIds_5131_);
lean_ctor_set(v___x_5132_, 1, v_anchorInfo_x3f_5118_);
v___x_5133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
return v___x_5133_;
}
v___jp_5134_:
{
lean_object* v___x_5135_; 
v___x_5135_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5113_, v___y_5128_);
if (lean_obj_tag(v_c_5114_) == 1)
{
lean_object* v_e_5136_; lean_object* v_binderType_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
lean_dec_ref(v___x_5135_);
lean_dec_ref(v___x_5113_);
v_e_5136_ = lean_ctor_get(v_c_5114_, 0);
lean_inc_ref(v_e_5136_);
lean_dec_ref_known(v_c_5114_, 2);
v_binderType_5137_ = lean_ctor_get(v_e_5136_, 1);
lean_inc_ref(v_binderType_5137_);
lean_dec_ref(v_e_5136_);
v___x_5138_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5137_);
v___x_5139_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5115_, v___x_5138_, v___y_5121_, v___y_5122_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref_known(v___x_5139_, 1);
v_mvarIds_5131_ = v_a_5140_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5148_; 
lean_dec(v_anchorInfo_x3f_5118_);
v_a_5141_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5143_ = v___x_5139_;
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5139_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5146_; 
if (v_isShared_5144_ == 0)
{
v___x_5146_ = v___x_5143_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5141_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
}
else
{
lean_object* v_a_5149_; uint8_t v___x_5150_; 
lean_dec_ref(v_c_5114_);
v_a_5149_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5149_);
lean_dec_ref(v___x_5135_);
v___x_5150_ = lean_unbox(v_a_5149_);
lean_dec(v_a_5149_);
if (v___x_5150_ == 0)
{
lean_object* v___x_5151_; 
v___x_5151_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5113_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; lean_object* v___x_5153_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
lean_dec_ref_known(v___x_5151_, 1);
v___x_5153_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5115_, v_a_5152_, v___y_5121_, v___y_5122_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v_a_5154_; 
v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
lean_inc(v_a_5154_);
lean_dec_ref_known(v___x_5153_, 1);
v_mvarIds_5131_ = v_a_5154_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
lean_dec(v_anchorInfo_x3f_5118_);
v_a_5155_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5153_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5153_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
v_a_5163_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5151_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5151_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
else
{
lean_object* v___x_5171_; 
v___x_5171_ = l_Lean_Meta_Grind_casesMatch(v_a_5115_, v___x_5113_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc(v_a_5172_);
lean_dec_ref_known(v___x_5171_, 1);
v_mvarIds_5131_ = v_a_5172_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec(v_anchorInfo_x3f_5118_);
v_a_5173_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5171_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5171_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5248_ = _args[0];
lean_object* v_c_5249_ = _args[1];
lean_object* v_a_5250_ = _args[2];
lean_object* v_numCases_5251_ = _args[3];
lean_object* v_isRec_5252_ = _args[4];
lean_object* v_anchorInfo_x3f_5253_ = _args[5];
lean_object* v___y_5254_ = _args[6];
lean_object* v___y_5255_ = _args[7];
lean_object* v___y_5256_ = _args[8];
lean_object* v___y_5257_ = _args[9];
lean_object* v___y_5258_ = _args[10];
lean_object* v___y_5259_ = _args[11];
lean_object* v___y_5260_ = _args[12];
lean_object* v___y_5261_ = _args[13];
lean_object* v___y_5262_ = _args[14];
lean_object* v___y_5263_ = _args[15];
lean_object* v___y_5264_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5265_; lean_object* v_res_5266_; 
v_isRec_boxed_5265_ = lean_unbox(v_isRec_5252_);
v_res_5266_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5248_, v_c_5249_, v_a_5250_, v_numCases_5251_, v_isRec_boxed_5265_, v_anchorInfo_x3f_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec(v___y_5254_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5267_, uint8_t v_trace_5268_, lean_object* v___f_5269_, lean_object* v_c_5270_, lean_object* v_candidates_x3f_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v___x_5282_; lean_object* v___y_5284_; 
v___x_5282_ = lean_st_mk_ref(v_goal_5267_);
if (v_trace_5268_ == 0)
{
lean_object* v___x_5303_; lean_object* v___x_5304_; 
lean_dec(v_candidates_x3f_5271_);
v___x_5303_ = lean_box(0);
lean_inc(v___x_5282_);
v___x_5304_ = lean_apply_12(v___f_5269_, v___x_5303_, v___x_5282_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, lean_box(0));
v___y_5284_ = v___x_5304_;
goto v___jp_5283_;
}
else
{
lean_object* v___x_5305_; 
v___x_5305_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5270_, v_candidates_x3f_5271_, v___x_5282_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref_known(v___x_5305_, 1);
v___x_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5307_, 0, v_a_5306_);
lean_inc(v___x_5282_);
v___x_5308_ = lean_apply_12(v___f_5269_, v___x_5307_, v___x_5282_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, lean_box(0));
v___y_5284_ = v___x_5308_;
goto v___jp_5283_;
}
else
{
lean_object* v_a_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5316_; 
lean_dec(v___x_5282_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___f_5269_);
v_a_5309_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5316_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5316_ == 0)
{
v___x_5311_ = v___x_5305_;
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_a_5309_);
lean_dec(v___x_5305_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5314_; 
if (v_isShared_5312_ == 0)
{
v___x_5314_ = v___x_5311_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
}
}
v___jp_5283_:
{
if (lean_obj_tag(v___y_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5294_; 
v_a_5285_ = lean_ctor_get(v___y_5284_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___y_5284_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5287_ = v___y_5284_;
v_isShared_5288_ = v_isSharedCheck_5294_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___y_5284_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5294_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5292_; 
v___x_5289_ = lean_st_ref_get(v___x_5282_);
lean_dec(v___x_5282_);
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v_a_5285_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5290_);
v___x_5292_ = v___x_5287_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v___x_5290_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
lean_dec(v___x_5282_);
v_a_5295_ = lean_ctor_get(v___y_5284_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___y_5284_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___y_5284_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___y_5284_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5317_, lean_object* v_trace_5318_, lean_object* v___f_5319_, lean_object* v_c_5320_, lean_object* v_candidates_x3f_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
uint8_t v_trace_boxed_5332_; lean_object* v_res_5333_; 
v_trace_boxed_5332_ = lean_unbox(v_trace_5318_);
v_res_5333_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5317_, v_trace_boxed_5332_, v___f_5319_, v_c_5320_, v_candidates_x3f_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
lean_dec_ref(v_c_5320_);
return v_res_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(lean_object* v_x_5334_, lean_object* v_x_5335_, lean_object* v_x_5336_, lean_object* v_x_5337_){
_start:
{
lean_object* v_ks_5338_; lean_object* v_vs_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5363_; 
v_ks_5338_ = lean_ctor_get(v_x_5334_, 0);
v_vs_5339_ = lean_ctor_get(v_x_5334_, 1);
v_isSharedCheck_5363_ = !lean_is_exclusive(v_x_5334_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5341_ = v_x_5334_;
v_isShared_5342_ = v_isSharedCheck_5363_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_vs_5339_);
lean_inc(v_ks_5338_);
lean_dec(v_x_5334_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5363_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; uint8_t v___x_5344_; 
v___x_5343_ = lean_array_get_size(v_ks_5338_);
v___x_5344_ = lean_nat_dec_lt(v_x_5335_, v___x_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
lean_dec(v_x_5335_);
v___x_5345_ = lean_array_push(v_ks_5338_, v_x_5336_);
v___x_5346_ = lean_array_push(v_vs_5339_, v_x_5337_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5346_);
lean_ctor_set(v___x_5341_, 0, v___x_5345_);
v___x_5348_ = v___x_5341_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5345_);
lean_ctor_set(v_reuseFailAlloc_5349_, 1, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
else
{
lean_object* v_k_x27_5350_; uint8_t v___x_5351_; 
v_k_x27_5350_ = lean_array_fget_borrowed(v_ks_5338_, v_x_5335_);
v___x_5351_ = l_Lean_instBEqMVarId_beq(v_x_5336_, v_k_x27_5350_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5353_; 
if (v_isShared_5342_ == 0)
{
v___x_5353_ = v___x_5341_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_ks_5338_);
lean_ctor_set(v_reuseFailAlloc_5357_, 1, v_vs_5339_);
v___x_5353_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5354_ = lean_unsigned_to_nat(1u);
v___x_5355_ = lean_nat_add(v_x_5335_, v___x_5354_);
lean_dec(v_x_5335_);
v_x_5334_ = v___x_5353_;
v_x_5335_ = v___x_5355_;
goto _start;
}
}
else
{
lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5358_ = lean_array_fset(v_ks_5338_, v_x_5335_, v_x_5336_);
v___x_5359_ = lean_array_fset(v_vs_5339_, v_x_5335_, v_x_5337_);
lean_dec(v_x_5335_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5359_);
lean_ctor_set(v___x_5341_, 0, v___x_5358_);
v___x_5361_ = v___x_5341_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5362_, 1, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(lean_object* v_n_5364_, lean_object* v_k_5365_, lean_object* v_v_5366_){
_start:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5367_ = lean_unsigned_to_nat(0u);
v___x_5368_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(v_n_5364_, v___x_5367_, v_k_5365_, v_v_5366_);
return v___x_5368_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_5369_; 
v___x_5369_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(lean_object* v_x_5370_, size_t v_x_5371_, size_t v_x_5372_, lean_object* v_x_5373_, lean_object* v_x_5374_){
_start:
{
if (lean_obj_tag(v_x_5370_) == 0)
{
lean_object* v_es_5375_; size_t v___x_5376_; size_t v___x_5377_; lean_object* v_j_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v_es_5375_ = lean_ctor_get(v_x_5370_, 0);
v___x_5376_ = ((size_t)31ULL);
v___x_5377_ = lean_usize_land(v_x_5371_, v___x_5376_);
v_j_5378_ = lean_usize_to_nat(v___x_5377_);
v___x_5379_ = lean_array_get_size(v_es_5375_);
v___x_5380_ = lean_nat_dec_lt(v_j_5378_, v___x_5379_);
if (v___x_5380_ == 0)
{
lean_dec(v_j_5378_);
lean_dec(v_x_5374_);
lean_dec(v_x_5373_);
return v_x_5370_;
}
else
{
lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5419_; 
lean_inc_ref(v_es_5375_);
v_isSharedCheck_5419_ = !lean_is_exclusive(v_x_5370_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; 
v_unused_5420_ = lean_ctor_get(v_x_5370_, 0);
lean_dec(v_unused_5420_);
v___x_5382_ = v_x_5370_;
v_isShared_5383_ = v_isSharedCheck_5419_;
goto v_resetjp_5381_;
}
else
{
lean_dec(v_x_5370_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5419_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v_v_5384_; lean_object* v___x_5385_; lean_object* v_xs_x27_5386_; lean_object* v___y_5388_; 
v_v_5384_ = lean_array_fget(v_es_5375_, v_j_5378_);
v___x_5385_ = lean_box(0);
v_xs_x27_5386_ = lean_array_fset(v_es_5375_, v_j_5378_, v___x_5385_);
switch(lean_obj_tag(v_v_5384_))
{
case 0:
{
lean_object* v_key_5393_; lean_object* v_val_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5404_; 
v_key_5393_ = lean_ctor_get(v_v_5384_, 0);
v_val_5394_ = lean_ctor_get(v_v_5384_, 1);
v_isSharedCheck_5404_ = !lean_is_exclusive(v_v_5384_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5396_ = v_v_5384_;
v_isShared_5397_ = v_isSharedCheck_5404_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_val_5394_);
lean_inc(v_key_5393_);
lean_dec(v_v_5384_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5404_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
uint8_t v___x_5398_; 
v___x_5398_ = l_Lean_instBEqMVarId_beq(v_x_5373_, v_key_5393_);
if (v___x_5398_ == 0)
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
lean_del_object(v___x_5396_);
v___x_5399_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5393_, v_val_5394_, v_x_5373_, v_x_5374_);
v___x_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5399_);
v___y_5388_ = v___x_5400_;
goto v___jp_5387_;
}
else
{
lean_object* v___x_5402_; 
lean_dec(v_val_5394_);
lean_dec(v_key_5393_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v_x_5374_);
lean_ctor_set(v___x_5396_, 0, v_x_5373_);
v___x_5402_ = v___x_5396_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_x_5373_);
lean_ctor_set(v_reuseFailAlloc_5403_, 1, v_x_5374_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
v___y_5388_ = v___x_5402_;
goto v___jp_5387_;
}
}
}
}
case 1:
{
lean_object* v_node_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5417_; 
v_node_5405_ = lean_ctor_get(v_v_5384_, 0);
v_isSharedCheck_5417_ = !lean_is_exclusive(v_v_5384_);
if (v_isSharedCheck_5417_ == 0)
{
v___x_5407_ = v_v_5384_;
v_isShared_5408_ = v_isSharedCheck_5417_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_node_5405_);
lean_dec(v_v_5384_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5417_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
size_t v___x_5409_; size_t v___x_5410_; size_t v___x_5411_; size_t v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5415_; 
v___x_5409_ = ((size_t)5ULL);
v___x_5410_ = lean_usize_shift_right(v_x_5371_, v___x_5409_);
v___x_5411_ = ((size_t)1ULL);
v___x_5412_ = lean_usize_add(v_x_5372_, v___x_5411_);
v___x_5413_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_node_5405_, v___x_5410_, v___x_5412_, v_x_5373_, v_x_5374_);
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 0, v___x_5413_);
v___x_5415_ = v___x_5407_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5413_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
v___y_5388_ = v___x_5415_;
goto v___jp_5387_;
}
}
}
default: 
{
lean_object* v___x_5418_; 
v___x_5418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5418_, 0, v_x_5373_);
lean_ctor_set(v___x_5418_, 1, v_x_5374_);
v___y_5388_ = v___x_5418_;
goto v___jp_5387_;
}
}
v___jp_5387_:
{
lean_object* v___x_5389_; lean_object* v___x_5391_; 
v___x_5389_ = lean_array_fset(v_xs_x27_5386_, v_j_5378_, v___y_5388_);
lean_dec(v_j_5378_);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 0, v___x_5389_);
v___x_5391_ = v___x_5382_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
}
else
{
lean_object* v_ks_5421_; lean_object* v_vs_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5440_; 
v_ks_5421_ = lean_ctor_get(v_x_5370_, 0);
v_vs_5422_ = lean_ctor_get(v_x_5370_, 1);
v_isSharedCheck_5440_ = !lean_is_exclusive(v_x_5370_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5424_ = v_x_5370_;
v_isShared_5425_ = v_isSharedCheck_5440_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_vs_5422_);
lean_inc(v_ks_5421_);
lean_dec(v_x_5370_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5440_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_ks_5421_);
lean_ctor_set(v_reuseFailAlloc_5439_, 1, v_vs_5422_);
v___x_5427_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v_newNode_5428_; size_t v___x_5429_; uint8_t v___x_5430_; 
v_newNode_5428_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(v___x_5427_, v_x_5373_, v_x_5374_);
v___x_5429_ = ((size_t)7ULL);
v___x_5430_ = lean_usize_dec_le(v___x_5429_, v_x_5372_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; 
v___x_5431_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5428_);
v___x_5432_ = lean_unsigned_to_nat(4u);
v___x_5433_ = lean_nat_dec_lt(v___x_5431_, v___x_5432_);
lean_dec(v___x_5431_);
if (v___x_5433_ == 0)
{
lean_object* v_ks_5434_; lean_object* v_vs_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v_ks_5434_ = lean_ctor_get(v_newNode_5428_, 0);
lean_inc_ref(v_ks_5434_);
v_vs_5435_ = lean_ctor_get(v_newNode_5428_, 1);
lean_inc_ref(v_vs_5435_);
lean_dec_ref(v_newNode_5428_);
v___x_5436_ = lean_unsigned_to_nat(0u);
v___x_5437_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0);
v___x_5438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(v_x_5372_, v_ks_5434_, v_vs_5435_, v___x_5436_, v___x_5437_);
lean_dec_ref(v_vs_5435_);
lean_dec_ref(v_ks_5434_);
return v___x_5438_;
}
else
{
return v_newNode_5428_;
}
}
else
{
return v_newNode_5428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(size_t v_depth_5441_, lean_object* v_keys_5442_, lean_object* v_vals_5443_, lean_object* v_i_5444_, lean_object* v_entries_5445_){
_start:
{
lean_object* v___x_5446_; uint8_t v___x_5447_; 
v___x_5446_ = lean_array_get_size(v_keys_5442_);
v___x_5447_ = lean_nat_dec_lt(v_i_5444_, v___x_5446_);
if (v___x_5447_ == 0)
{
lean_dec(v_i_5444_);
return v_entries_5445_;
}
else
{
lean_object* v_k_5448_; lean_object* v_v_5449_; uint64_t v___x_5450_; size_t v_h_5451_; size_t v___x_5452_; lean_object* v___x_5453_; size_t v___x_5454_; size_t v___x_5455_; size_t v___x_5456_; size_t v_h_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v_k_5448_ = lean_array_fget_borrowed(v_keys_5442_, v_i_5444_);
v_v_5449_ = lean_array_fget_borrowed(v_vals_5443_, v_i_5444_);
v___x_5450_ = l_Lean_instHashableMVarId_hash(v_k_5448_);
v_h_5451_ = lean_uint64_to_usize(v___x_5450_);
v___x_5452_ = ((size_t)5ULL);
v___x_5453_ = lean_unsigned_to_nat(1u);
v___x_5454_ = ((size_t)1ULL);
v___x_5455_ = lean_usize_sub(v_depth_5441_, v___x_5454_);
v___x_5456_ = lean_usize_mul(v___x_5452_, v___x_5455_);
v_h_5457_ = lean_usize_shift_right(v_h_5451_, v___x_5456_);
v___x_5458_ = lean_nat_add(v_i_5444_, v___x_5453_);
lean_dec(v_i_5444_);
lean_inc(v_v_5449_);
lean_inc(v_k_5448_);
v___x_5459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_entries_5445_, v_h_5457_, v_depth_5441_, v_k_5448_, v_v_5449_);
v_i_5444_ = v___x_5458_;
v_entries_5445_ = v___x_5459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_depth_5461_, lean_object* v_keys_5462_, lean_object* v_vals_5463_, lean_object* v_i_5464_, lean_object* v_entries_5465_){
_start:
{
size_t v_depth_boxed_5466_; lean_object* v_res_5467_; 
v_depth_boxed_5466_ = lean_unbox_usize(v_depth_5461_);
lean_dec(v_depth_5461_);
v_res_5467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(v_depth_boxed_5466_, v_keys_5462_, v_vals_5463_, v_i_5464_, v_entries_5465_);
lean_dec_ref(v_vals_5463_);
lean_dec_ref(v_keys_5462_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___boxed(lean_object* v_x_5468_, lean_object* v_x_5469_, lean_object* v_x_5470_, lean_object* v_x_5471_, lean_object* v_x_5472_){
_start:
{
size_t v_x_103379__boxed_5473_; size_t v_x_103380__boxed_5474_; lean_object* v_res_5475_; 
v_x_103379__boxed_5473_ = lean_unbox_usize(v_x_5469_);
lean_dec(v_x_5469_);
v_x_103380__boxed_5474_ = lean_unbox_usize(v_x_5470_);
lean_dec(v_x_5470_);
v_res_5475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_x_5468_, v_x_103379__boxed_5473_, v_x_103380__boxed_5474_, v_x_5471_, v_x_5472_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(lean_object* v_x_5476_, lean_object* v_x_5477_, lean_object* v_x_5478_){
_start:
{
uint64_t v___x_5479_; size_t v___x_5480_; size_t v___x_5481_; lean_object* v___x_5482_; 
v___x_5479_ = l_Lean_instHashableMVarId_hash(v_x_5477_);
v___x_5480_ = lean_uint64_to_usize(v___x_5479_);
v___x_5481_ = ((size_t)1ULL);
v___x_5482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_x_5476_, v___x_5480_, v___x_5481_, v_x_5477_, v_x_5478_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(lean_object* v_mvarId_5483_, lean_object* v_val_5484_, lean_object* v___y_5485_){
_start:
{
lean_object* v___x_5487_; lean_object* v_mctx_5488_; lean_object* v_cache_5489_; lean_object* v_zetaDeltaFVarIds_5490_; lean_object* v_postponed_5491_; lean_object* v_diag_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5522_; 
v___x_5487_ = lean_st_ref_take(v___y_5485_);
v_mctx_5488_ = lean_ctor_get(v___x_5487_, 0);
v_cache_5489_ = lean_ctor_get(v___x_5487_, 1);
v_zetaDeltaFVarIds_5490_ = lean_ctor_get(v___x_5487_, 2);
v_postponed_5491_ = lean_ctor_get(v___x_5487_, 3);
v_diag_5492_ = lean_ctor_get(v___x_5487_, 4);
v_isSharedCheck_5522_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5522_ == 0)
{
v___x_5494_ = v___x_5487_;
v_isShared_5495_ = v_isSharedCheck_5522_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_diag_5492_);
lean_inc(v_postponed_5491_);
lean_inc(v_zetaDeltaFVarIds_5490_);
lean_inc(v_cache_5489_);
lean_inc(v_mctx_5488_);
lean_dec(v___x_5487_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5522_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v_depth_5496_; lean_object* v_levelAssignDepth_5497_; lean_object* v_lmvarCounter_5498_; lean_object* v_mvarCounter_5499_; lean_object* v_lDecls_5500_; lean_object* v_decls_5501_; lean_object* v_userNames_5502_; lean_object* v_lAssignment_5503_; lean_object* v_eAssignment_5504_; lean_object* v_dAssignment_5505_; lean_object* v_instanceTypedMVars_5506_; lean_object* v_synthNormMemo_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5521_; 
v_depth_5496_ = lean_ctor_get(v_mctx_5488_, 0);
v_levelAssignDepth_5497_ = lean_ctor_get(v_mctx_5488_, 1);
v_lmvarCounter_5498_ = lean_ctor_get(v_mctx_5488_, 2);
v_mvarCounter_5499_ = lean_ctor_get(v_mctx_5488_, 3);
v_lDecls_5500_ = lean_ctor_get(v_mctx_5488_, 4);
v_decls_5501_ = lean_ctor_get(v_mctx_5488_, 5);
v_userNames_5502_ = lean_ctor_get(v_mctx_5488_, 6);
v_lAssignment_5503_ = lean_ctor_get(v_mctx_5488_, 7);
v_eAssignment_5504_ = lean_ctor_get(v_mctx_5488_, 8);
v_dAssignment_5505_ = lean_ctor_get(v_mctx_5488_, 9);
v_instanceTypedMVars_5506_ = lean_ctor_get(v_mctx_5488_, 10);
v_synthNormMemo_5507_ = lean_ctor_get(v_mctx_5488_, 11);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_mctx_5488_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5509_ = v_mctx_5488_;
v_isShared_5510_ = v_isSharedCheck_5521_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_synthNormMemo_5507_);
lean_inc(v_instanceTypedMVars_5506_);
lean_inc(v_dAssignment_5505_);
lean_inc(v_eAssignment_5504_);
lean_inc(v_lAssignment_5503_);
lean_inc(v_userNames_5502_);
lean_inc(v_decls_5501_);
lean_inc(v_lDecls_5500_);
lean_inc(v_mvarCounter_5499_);
lean_inc(v_lmvarCounter_5498_);
lean_inc(v_levelAssignDepth_5497_);
lean_inc(v_depth_5496_);
lean_dec(v_mctx_5488_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5521_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5514_; 
v___x_5511_ = lean_box(0);
v___x_5512_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(v_eAssignment_5504_, v_mvarId_5483_, v_val_5484_);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 8, v___x_5512_);
v___x_5514_ = v___x_5509_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_depth_5496_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_levelAssignDepth_5497_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_lmvarCounter_5498_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_mvarCounter_5499_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v_lDecls_5500_);
lean_ctor_set(v_reuseFailAlloc_5520_, 5, v_decls_5501_);
lean_ctor_set(v_reuseFailAlloc_5520_, 6, v_userNames_5502_);
lean_ctor_set(v_reuseFailAlloc_5520_, 7, v_lAssignment_5503_);
lean_ctor_set(v_reuseFailAlloc_5520_, 8, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5520_, 9, v_dAssignment_5505_);
lean_ctor_set(v_reuseFailAlloc_5520_, 10, v_instanceTypedMVars_5506_);
lean_ctor_set(v_reuseFailAlloc_5520_, 11, v_synthNormMemo_5507_);
v___x_5514_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; 
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 0, v___x_5514_);
v___x_5516_ = v___x_5494_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5514_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v_cache_5489_);
lean_ctor_set(v_reuseFailAlloc_5519_, 2, v_zetaDeltaFVarIds_5490_);
lean_ctor_set(v_reuseFailAlloc_5519_, 3, v_postponed_5491_);
lean_ctor_set(v_reuseFailAlloc_5519_, 4, v_diag_5492_);
v___x_5516_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; 
v___x_5517_ = lean_st_ref_put(v___y_5485_, v___x_5516_);
v___x_5518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5511_);
return v___x_5518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg___boxed(lean_object* v_mvarId_5523_, lean_object* v_val_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_5523_, v_val_5524_, v___y_5525_);
lean_dec(v___y_5525_);
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v___x_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_){
_start:
{
if (lean_obj_tag(v_a_5529_) == 0)
{
lean_object* v___x_5531_; 
v___x_5531_ = l_List_reverse___redArg(v_a_5530_);
return v___x_5531_;
}
else
{
lean_object* v_head_5532_; lean_object* v_toGoalState_5533_; lean_object* v_tail_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5583_; 
v_head_5532_ = lean_ctor_get(v_a_5529_, 0);
lean_inc(v_head_5532_);
v_toGoalState_5533_ = lean_ctor_get(v_head_5532_, 0);
lean_inc_ref(v_toGoalState_5533_);
v_tail_5534_ = lean_ctor_get(v_a_5529_, 1);
v_isSharedCheck_5583_ = !lean_is_exclusive(v_a_5529_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; 
v_unused_5584_ = lean_ctor_get(v_a_5529_, 0);
lean_dec(v_unused_5584_);
v___x_5536_ = v_a_5529_;
v_isShared_5537_ = v_isSharedCheck_5583_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_tail_5534_);
lean_dec(v_a_5529_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5583_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v_mvarId_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5581_; 
v_mvarId_5538_ = lean_ctor_get(v_head_5532_, 1);
v_isSharedCheck_5581_ = !lean_is_exclusive(v_head_5532_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v_head_5532_, 0);
lean_dec(v_unused_5582_);
v___x_5540_ = v_head_5532_;
v_isShared_5541_ = v_isSharedCheck_5581_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_mvarId_5538_);
lean_dec(v_head_5532_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5581_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v_nextDeclIdx_5542_; lean_object* v_enodeMap_5543_; lean_object* v_exprs_5544_; lean_object* v_parents_5545_; lean_object* v_congrTable_5546_; lean_object* v_appMap_5547_; lean_object* v_indicesFound_5548_; lean_object* v_toProcess_5549_; lean_object* v_internalizing_5550_; uint8_t v_inconsistent_5551_; lean_object* v_nextIdx_5552_; lean_object* v_newRawFacts_5553_; lean_object* v_facts_5554_; lean_object* v_extThms_5555_; lean_object* v_ematch_5556_; lean_object* v_inj_5557_; lean_object* v_split_5558_; lean_object* v_clean_5559_; lean_object* v_sstates_5560_; lean_object* v_goalStack_5561_; uint64_t v_introBase_5562_; lean_object* v_numIntros_5563_; lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5580_; 
v_nextDeclIdx_5542_ = lean_ctor_get(v_toGoalState_5533_, 0);
v_enodeMap_5543_ = lean_ctor_get(v_toGoalState_5533_, 1);
v_exprs_5544_ = lean_ctor_get(v_toGoalState_5533_, 2);
v_parents_5545_ = lean_ctor_get(v_toGoalState_5533_, 3);
v_congrTable_5546_ = lean_ctor_get(v_toGoalState_5533_, 4);
v_appMap_5547_ = lean_ctor_get(v_toGoalState_5533_, 5);
v_indicesFound_5548_ = lean_ctor_get(v_toGoalState_5533_, 6);
v_toProcess_5549_ = lean_ctor_get(v_toGoalState_5533_, 7);
v_internalizing_5550_ = lean_ctor_get(v_toGoalState_5533_, 8);
v_inconsistent_5551_ = lean_ctor_get_uint8(v_toGoalState_5533_, sizeof(void*)*20 + 8);
v_nextIdx_5552_ = lean_ctor_get(v_toGoalState_5533_, 9);
v_newRawFacts_5553_ = lean_ctor_get(v_toGoalState_5533_, 10);
v_facts_5554_ = lean_ctor_get(v_toGoalState_5533_, 11);
v_extThms_5555_ = lean_ctor_get(v_toGoalState_5533_, 12);
v_ematch_5556_ = lean_ctor_get(v_toGoalState_5533_, 13);
v_inj_5557_ = lean_ctor_get(v_toGoalState_5533_, 14);
v_split_5558_ = lean_ctor_get(v_toGoalState_5533_, 15);
v_clean_5559_ = lean_ctor_get(v_toGoalState_5533_, 16);
v_sstates_5560_ = lean_ctor_get(v_toGoalState_5533_, 17);
v_goalStack_5561_ = lean_ctor_get(v_toGoalState_5533_, 18);
v_introBase_5562_ = lean_ctor_get_uint64(v_toGoalState_5533_, sizeof(void*)*20);
v_numIntros_5563_ = lean_ctor_get(v_toGoalState_5533_, 19);
v_isSharedCheck_5580_ = !lean_is_exclusive(v_toGoalState_5533_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5565_ = v_toGoalState_5533_;
v_isShared_5566_ = v_isSharedCheck_5580_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_numIntros_5563_);
lean_inc(v_goalStack_5561_);
lean_inc(v_sstates_5560_);
lean_inc(v_clean_5559_);
lean_inc(v_split_5558_);
lean_inc(v_inj_5557_);
lean_inc(v_ematch_5556_);
lean_inc(v_extThms_5555_);
lean_inc(v_facts_5554_);
lean_inc(v_newRawFacts_5553_);
lean_inc(v_nextIdx_5552_);
lean_inc(v_internalizing_5550_);
lean_inc(v_toProcess_5549_);
lean_inc(v_indicesFound_5548_);
lean_inc(v_appMap_5547_);
lean_inc(v_congrTable_5546_);
lean_inc(v_parents_5545_);
lean_inc(v_exprs_5544_);
lean_inc(v_enodeMap_5543_);
lean_inc(v_nextDeclIdx_5542_);
lean_dec(v_toGoalState_5533_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5580_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5571_; 
v___x_5567_ = lean_unsigned_to_nat(0u);
v___x_5568_ = lean_array_get_size(v___x_5528_);
v___x_5569_ = l_Array_extract___redArg(v_goalStack_5561_, v___x_5567_, v___x_5568_);
lean_dec_ref(v_goalStack_5561_);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 18, v___x_5569_);
v___x_5571_ = v___x_5565_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_nextDeclIdx_5542_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v_enodeMap_5543_);
lean_ctor_set(v_reuseFailAlloc_5579_, 2, v_exprs_5544_);
lean_ctor_set(v_reuseFailAlloc_5579_, 3, v_parents_5545_);
lean_ctor_set(v_reuseFailAlloc_5579_, 4, v_congrTable_5546_);
lean_ctor_set(v_reuseFailAlloc_5579_, 5, v_appMap_5547_);
lean_ctor_set(v_reuseFailAlloc_5579_, 6, v_indicesFound_5548_);
lean_ctor_set(v_reuseFailAlloc_5579_, 7, v_toProcess_5549_);
lean_ctor_set(v_reuseFailAlloc_5579_, 8, v_internalizing_5550_);
lean_ctor_set(v_reuseFailAlloc_5579_, 9, v_nextIdx_5552_);
lean_ctor_set(v_reuseFailAlloc_5579_, 10, v_newRawFacts_5553_);
lean_ctor_set(v_reuseFailAlloc_5579_, 11, v_facts_5554_);
lean_ctor_set(v_reuseFailAlloc_5579_, 12, v_extThms_5555_);
lean_ctor_set(v_reuseFailAlloc_5579_, 13, v_ematch_5556_);
lean_ctor_set(v_reuseFailAlloc_5579_, 14, v_inj_5557_);
lean_ctor_set(v_reuseFailAlloc_5579_, 15, v_split_5558_);
lean_ctor_set(v_reuseFailAlloc_5579_, 16, v_clean_5559_);
lean_ctor_set(v_reuseFailAlloc_5579_, 17, v_sstates_5560_);
lean_ctor_set(v_reuseFailAlloc_5579_, 18, v___x_5569_);
lean_ctor_set(v_reuseFailAlloc_5579_, 19, v_numIntros_5563_);
lean_ctor_set_uint8(v_reuseFailAlloc_5579_, sizeof(void*)*20 + 8, v_inconsistent_5551_);
lean_ctor_set_uint64(v_reuseFailAlloc_5579_, sizeof(void*)*20, v_introBase_5562_);
v___x_5571_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
lean_object* v___x_5573_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 0, v___x_5571_);
v___x_5573_ = v___x_5540_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_mvarId_5538_);
v___x_5573_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
lean_object* v___x_5575_; 
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 1, v_a_5530_);
lean_ctor_set(v___x_5536_, 0, v___x_5573_);
v___x_5575_ = v___x_5536_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v_a_5530_);
v___x_5575_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
v_a_5529_ = v_tail_5534_;
v_a_5530_ = v___x_5575_;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v___x_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_){
_start:
{
lean_object* v_res_5588_; 
v_res_5588_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_5585_, v_a_5586_, v_a_5587_);
lean_dec_ref(v___x_5585_);
return v_res_5588_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(lean_object* v___x_5589_, lean_object* v_gs_5590_){
_start:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5591_ = lean_box(0);
v___x_5592_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_5589_, v_gs_5590_, v___x_5591_);
return v___x_5592_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_5593_, lean_object* v_gs_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(v___x_5593_, v_gs_5594_);
lean_dec_ref(v___x_5593_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_kp_5596_, lean_object* v_a_5597_, lean_object* v_goal_5598_, lean_object* v_snd_5599_, lean_object* v___x_5600_, uint8_t v_stopAtFirstFailure_5601_, lean_object* v___x_5602_, lean_object* v_as_x27_5603_, lean_object* v_b_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_){
_start:
{
if (lean_obj_tag(v_as_x27_5603_) == 0)
{
lean_object* v___x_5615_; 
lean_dec(v___x_5600_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v___x_5615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5615_, 0, v_b_5604_);
return v___x_5615_;
}
else
{
lean_object* v_snd_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5882_; 
v_snd_5616_ = lean_ctor_get(v_b_5604_, 1);
v_isSharedCheck_5882_ = !lean_is_exclusive(v_b_5604_);
if (v_isSharedCheck_5882_ == 0)
{
lean_object* v_unused_5883_; 
v_unused_5883_ = lean_ctor_get(v_b_5604_, 0);
lean_dec(v_unused_5883_);
v___x_5618_ = v_b_5604_;
v_isShared_5619_ = v_isSharedCheck_5882_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_snd_5616_);
lean_dec(v_b_5604_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5882_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v_snd_5620_; lean_object* v_head_5621_; lean_object* v_tail_5622_; lean_object* v_fst_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5880_; 
v_snd_5620_ = lean_ctor_get(v_snd_5616_, 1);
lean_inc(v_snd_5620_);
v_head_5621_ = lean_ctor_get(v_as_x27_5603_, 0);
v_tail_5622_ = lean_ctor_get(v_as_x27_5603_, 1);
v_fst_5623_ = lean_ctor_get(v_snd_5616_, 0);
v_isSharedCheck_5880_ = !lean_is_exclusive(v_snd_5616_);
if (v_isSharedCheck_5880_ == 0)
{
lean_object* v_unused_5881_; 
v_unused_5881_ = lean_ctor_get(v_snd_5616_, 1);
lean_dec(v_unused_5881_);
v___x_5625_ = v_snd_5616_;
v_isShared_5626_ = v_isSharedCheck_5880_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_fst_5623_);
lean_dec(v_snd_5616_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5880_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v_fst_5627_; lean_object* v_snd_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5879_; 
v_fst_5627_ = lean_ctor_get(v_snd_5620_, 0);
v_snd_5628_ = lean_ctor_get(v_snd_5620_, 1);
v_isSharedCheck_5879_ = !lean_is_exclusive(v_snd_5620_);
if (v_isSharedCheck_5879_ == 0)
{
v___x_5630_ = v_snd_5620_;
v_isShared_5631_ = v_isSharedCheck_5879_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_snd_5628_);
lean_inc(v_fst_5627_);
lean_dec(v_snd_5620_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5879_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5632_; lean_object* v___x_5633_; 
v___x_5632_ = lean_box(0);
lean_inc_ref(v_kp_5596_);
lean_inc(v___y_5613_);
lean_inc_ref(v___y_5612_);
lean_inc(v___y_5611_);
lean_inc_ref(v___y_5610_);
lean_inc(v___y_5609_);
lean_inc_ref(v___y_5608_);
lean_inc(v___y_5607_);
lean_inc_ref(v___y_5606_);
lean_inc(v___y_5605_);
lean_inc(v_head_5621_);
v___x_5633_ = lean_apply_11(v_kp_5596_, v_head_5621_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, lean_box(0));
if (lean_obj_tag(v___x_5633_) == 0)
{
lean_object* v_a_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5870_; 
v_a_5634_ = lean_ctor_get(v___x_5633_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5633_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5636_ = v___x_5633_;
v_isShared_5637_ = v_isSharedCheck_5870_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_a_5634_);
lean_dec(v___x_5633_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5870_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
if (lean_obj_tag(v_a_5634_) == 0)
{
lean_object* v_seq_5638_; lean_object* v_ncb_x3f_5640_; lean_object* v_mvarId_5663_; lean_object* v___x_5664_; 
lean_del_object(v___x_5636_);
v_seq_5638_ = lean_ctor_get(v_a_5634_, 0);
v_mvarId_5663_ = lean_ctor_get(v_head_5621_, 1);
lean_inc(v_mvarId_5663_);
v___x_5664_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5663_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v_a_5665_; 
v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
lean_inc(v_a_5665_);
lean_dec_ref_known(v___x_5664_, 1);
if (lean_obj_tag(v_a_5665_) == 1)
{
lean_object* v_val_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5739_; 
v_val_5666_ = lean_ctor_get(v_a_5665_, 0);
v_isSharedCheck_5739_ = !lean_is_exclusive(v_a_5665_);
if (v_isSharedCheck_5739_ == 0)
{
v___x_5668_ = v_a_5665_;
v_isShared_5669_ = v_isSharedCheck_5739_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_val_5666_);
lean_dec(v_a_5665_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5739_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5670_; 
lean_inc(v_seq_5638_);
lean_inc_ref(v_goal_5598_);
lean_inc(v_a_5597_);
v___x_5670_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_5597_, v_goal_5598_, v_seq_5638_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v_a_5671_; uint8_t v___x_5672_; 
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
lean_inc(v_a_5671_);
lean_dec_ref_known(v___x_5670_, 1);
v___x_5672_ = lean_unbox(v_a_5671_);
lean_dec(v_a_5671_);
if (v___x_5672_ == 0)
{
lean_inc(v_seq_5638_);
lean_dec_ref_known(v_a_5634_, 1);
if (lean_obj_tag(v_snd_5628_) == 0)
{
lean_object* v___x_5673_; 
v___x_5673_ = l_Lean_Meta_Grind_saveState___redArg(v___y_5607_, v___y_5611_, v___y_5613_);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v_a_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5678_; 
v_a_5674_ = lean_ctor_get(v___x_5673_, 0);
lean_inc(v_a_5674_);
lean_dec_ref_known(v___x_5673_, 1);
lean_inc(v_seq_5638_);
v___x_5675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5675_, 0, v_val_5666_);
lean_ctor_set(v___x_5675_, 1, v_seq_5638_);
v___x_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5676_, 0, v_a_5674_);
lean_ctor_set(v___x_5676_, 1, v___x_5675_);
if (v_isShared_5669_ == 0)
{
lean_ctor_set(v___x_5668_, 0, v___x_5676_);
v___x_5678_ = v___x_5668_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5676_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
v_ncb_x3f_5640_ = v___x_5678_;
goto v___jp_5639_;
}
}
else
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5687_; 
lean_del_object(v___x_5668_);
lean_dec(v_val_5666_);
lean_dec(v_seq_5638_);
lean_del_object(v___x_5630_);
lean_dec(v_fst_5627_);
lean_del_object(v___x_5625_);
lean_dec(v_fst_5623_);
lean_del_object(v___x_5618_);
lean_dec(v___x_5600_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v_a_5680_ = lean_ctor_get(v___x_5673_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5682_ = v___x_5673_;
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5673_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5683_ == 0)
{
v___x_5685_ = v___x_5682_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_a_5680_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
else
{
lean_del_object(v___x_5668_);
lean_dec(v_val_5666_);
v_ncb_x3f_5640_ = v_snd_5628_;
goto v___jp_5639_;
}
}
else
{
lean_object* v___x_5688_; 
lean_del_object(v___x_5630_);
lean_del_object(v___x_5625_);
lean_del_object(v___x_5618_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v___x_5688_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5599_, v___y_5607_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_object* v_a_5689_; lean_object* v___x_5690_; 
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
lean_inc(v_a_5689_);
lean_dec_ref_known(v___x_5688_, 1);
v___x_5690_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5689_, v_val_5666_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
if (lean_obj_tag(v___x_5690_) == 0)
{
lean_object* v_a_5691_; lean_object* v___x_5692_; 
v_a_5691_ = lean_ctor_get(v___x_5690_, 0);
lean_inc(v_a_5691_);
lean_dec_ref_known(v___x_5690_, 1);
v___x_5692_ = l_Lean_MVarId_assignFalseProof(v___x_5600_, v_a_5691_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5705_; 
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; 
v_unused_5706_ = lean_ctor_get(v___x_5692_, 0);
lean_dec(v_unused_5706_);
v___x_5694_ = v___x_5692_;
v_isShared_5695_ = v_isSharedCheck_5705_;
goto v_resetjp_5693_;
}
else
{
lean_dec(v___x_5692_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5705_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v___x_5697_; 
if (v_isShared_5669_ == 0)
{
lean_ctor_set(v___x_5668_, 0, v_a_5634_);
v___x_5697_ = v___x_5668_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5634_);
v___x_5697_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5702_; 
v___x_5698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5698_, 0, v_fst_5627_);
lean_ctor_set(v___x_5698_, 1, v_snd_5628_);
v___x_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5699_, 0, v_fst_5623_);
lean_ctor_set(v___x_5699_, 1, v___x_5698_);
v___x_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5697_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 0, v___x_5700_);
v___x_5702_ = v___x_5694_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5700_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
else
{
lean_object* v_a_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5714_; 
lean_del_object(v___x_5668_);
lean_dec_ref_known(v_a_5634_, 1);
lean_dec(v_snd_5628_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
v_a_5707_ = lean_ctor_get(v___x_5692_, 0);
v_isSharedCheck_5714_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5709_ = v___x_5692_;
v_isShared_5710_ = v_isSharedCheck_5714_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_a_5707_);
lean_dec(v___x_5692_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5714_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5712_; 
if (v_isShared_5710_ == 0)
{
v___x_5712_ = v___x_5709_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_a_5707_);
v___x_5712_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
return v___x_5712_;
}
}
}
}
else
{
lean_object* v_a_5715_; lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5722_; 
lean_del_object(v___x_5668_);
lean_dec_ref_known(v_a_5634_, 1);
lean_dec(v_snd_5628_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
lean_dec(v___x_5600_);
v_a_5715_ = lean_ctor_get(v___x_5690_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5690_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5717_ = v___x_5690_;
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
else
{
lean_inc(v_a_5715_);
lean_dec(v___x_5690_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5720_; 
if (v_isShared_5718_ == 0)
{
v___x_5720_ = v___x_5717_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
}
else
{
lean_object* v_a_5723_; lean_object* v___x_5725_; uint8_t v_isShared_5726_; uint8_t v_isSharedCheck_5730_; 
lean_del_object(v___x_5668_);
lean_dec(v_val_5666_);
lean_dec_ref_known(v_a_5634_, 1);
lean_dec(v_snd_5628_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
lean_dec(v___x_5600_);
v_a_5723_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5725_ = v___x_5688_;
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
else
{
lean_inc(v_a_5723_);
lean_dec(v___x_5688_);
v___x_5725_ = lean_box(0);
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
v_resetjp_5724_:
{
lean_object* v___x_5728_; 
if (v_isShared_5726_ == 0)
{
v___x_5728_ = v___x_5725_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
v___x_5728_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
return v___x_5728_;
}
}
}
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
lean_del_object(v___x_5668_);
lean_dec(v_val_5666_);
lean_dec_ref_known(v_a_5634_, 1);
lean_del_object(v___x_5630_);
lean_dec(v_snd_5628_);
lean_dec(v_fst_5627_);
lean_del_object(v___x_5625_);
lean_dec(v_fst_5623_);
lean_del_object(v___x_5618_);
lean_dec(v___x_5600_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v_a_5731_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5670_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5670_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5736_; 
if (v_isShared_5734_ == 0)
{
v___x_5736_ = v___x_5733_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
}
}
else
{
uint8_t v___x_5740_; 
lean_inc(v_seq_5638_);
lean_dec(v_a_5665_);
lean_dec_ref_known(v_a_5634_, 1);
lean_del_object(v___x_5630_);
lean_del_object(v___x_5625_);
lean_del_object(v___x_5618_);
v___x_5740_ = l_List_isEmpty___redArg(v_seq_5638_);
if (v___x_5740_ == 0)
{
lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; 
v___x_5741_ = lean_array_push(v_fst_5623_, v_seq_5638_);
v___x_5742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5742_, 0, v_fst_5627_);
lean_ctor_set(v___x_5742_, 1, v_snd_5628_);
v___x_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5741_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5632_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
v_as_x27_5603_ = v_tail_5622_;
v_b_5604_ = v___x_5744_;
goto _start;
}
else
{
lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; 
lean_dec(v_seq_5638_);
v___x_5746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5746_, 0, v_fst_5627_);
lean_ctor_set(v___x_5746_, 1, v_snd_5628_);
v___x_5747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5747_, 0, v_fst_5623_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5632_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v_as_x27_5603_ = v_tail_5622_;
v_b_5604_ = v___x_5748_;
goto _start;
}
}
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5757_; 
lean_dec_ref_known(v_a_5634_, 1);
lean_del_object(v___x_5630_);
lean_dec(v_snd_5628_);
lean_dec(v_fst_5627_);
lean_del_object(v___x_5625_);
lean_dec(v_fst_5623_);
lean_del_object(v___x_5618_);
lean_dec(v___x_5600_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v_a_5750_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5752_ = v___x_5664_;
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5664_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5755_; 
if (v_isShared_5753_ == 0)
{
v___x_5755_ = v___x_5752_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
v___jp_5639_:
{
uint8_t v___x_5641_; 
v___x_5641_ = l_List_isEmpty___redArg(v_seq_5638_);
if (v___x_5641_ == 0)
{
lean_object* v___x_5642_; lean_object* v___x_5644_; 
v___x_5642_ = lean_array_push(v_fst_5623_, v_seq_5638_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v_ncb_x3f_5640_);
v___x_5644_ = v___x_5630_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_ncb_x3f_5640_);
v___x_5644_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
lean_object* v___x_5646_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5644_);
lean_ctor_set(v___x_5625_, 0, v___x_5642_);
v___x_5646_ = v___x_5625_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5642_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___x_5644_);
v___x_5646_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; 
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 1, v___x_5646_);
lean_ctor_set(v___x_5618_, 0, v___x_5632_);
v___x_5648_ = v___x_5618_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5632_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v___x_5646_);
v___x_5648_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
v_as_x27_5603_ = v_tail_5622_;
v_b_5604_ = v___x_5648_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_5654_; 
lean_dec(v_seq_5638_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v_ncb_x3f_5640_);
v___x_5654_ = v___x_5630_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_ncb_x3f_5640_);
v___x_5654_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5656_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5654_);
v___x_5656_ = v___x_5625_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v___x_5654_);
v___x_5656_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5658_; 
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 1, v___x_5656_);
lean_ctor_set(v___x_5618_, 0, v___x_5632_);
v___x_5658_ = v___x_5618_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5632_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5656_);
v___x_5658_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
v_as_x27_5603_ = v_tail_5622_;
v_b_5604_ = v___x_5658_;
goto _start;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_snd_5628_) == 1)
{
lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5833_; 
lean_del_object(v___x_5636_);
lean_del_object(v___x_5625_);
lean_del_object(v___x_5618_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v_isSharedCheck_5833_ = !lean_is_exclusive(v_a_5634_);
if (v_isSharedCheck_5833_ == 0)
{
lean_object* v_unused_5834_; 
v_unused_5834_ = lean_ctor_get(v_a_5634_, 0);
lean_dec(v_unused_5834_);
v___x_5759_ = v_a_5634_;
v_isShared_5760_ = v_isSharedCheck_5833_;
goto v_resetjp_5758_;
}
else
{
lean_dec(v_a_5634_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5833_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v_val_5761_; lean_object* v_snd_5762_; lean_object* v_fst_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5832_; 
v_val_5761_ = lean_ctor_get(v_snd_5628_, 0);
lean_inc(v_val_5761_);
v_snd_5762_ = lean_ctor_get(v_val_5761_, 1);
v_fst_5763_ = lean_ctor_get(v_val_5761_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v_val_5761_);
if (v_isSharedCheck_5832_ == 0)
{
v___x_5765_ = v_val_5761_;
v_isShared_5766_ = v_isSharedCheck_5832_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_snd_5762_);
lean_inc(v_fst_5763_);
lean_dec(v_val_5761_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5832_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v_fst_5767_; lean_object* v_snd_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_5831_; 
v_fst_5767_ = lean_ctor_get(v_snd_5762_, 0);
v_snd_5768_ = lean_ctor_get(v_snd_5762_, 1);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_snd_5762_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5770_ = v_snd_5762_;
v_isShared_5771_ = v_isSharedCheck_5831_;
goto v_resetjp_5769_;
}
else
{
lean_inc(v_snd_5768_);
lean_inc(v_fst_5767_);
lean_dec(v_snd_5762_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_5831_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
lean_object* v___x_5772_; 
v___x_5772_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_fst_5763_, v___y_5607_, v___y_5611_, v___y_5613_);
if (lean_obj_tag(v___x_5772_) == 0)
{
lean_object* v___x_5773_; 
lean_dec_ref_known(v___x_5772_, 1);
v___x_5773_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5599_, v___y_5607_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5775_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
lean_inc(v_a_5774_);
lean_dec_ref_known(v___x_5773_, 1);
v___x_5775_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5774_, v_fst_5767_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; lean_object* v___x_5777_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
lean_inc(v_a_5776_);
lean_dec_ref_known(v___x_5775_, 1);
v___x_5777_ = l_Lean_MVarId_assignFalseProof(v___x_5600_, v_a_5776_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5797_; 
v_isSharedCheck_5797_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5797_ == 0)
{
lean_object* v_unused_5798_; 
v_unused_5798_ = lean_ctor_get(v___x_5777_, 0);
lean_dec(v_unused_5798_);
v___x_5779_ = v___x_5777_;
v_isShared_5780_ = v_isSharedCheck_5797_;
goto v_resetjp_5778_;
}
else
{
lean_dec(v___x_5777_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5797_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set_tag(v___x_5759_, 0);
lean_ctor_set(v___x_5759_, 0, v_snd_5768_);
v___x_5782_ = v___x_5759_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_snd_5768_);
v___x_5782_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
lean_object* v___x_5783_; lean_object* v___x_5785_; 
v___x_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5783_, 0, v___x_5782_);
if (v_isShared_5771_ == 0)
{
lean_ctor_set(v___x_5770_, 1, v_snd_5628_);
lean_ctor_set(v___x_5770_, 0, v_fst_5627_);
v___x_5785_ = v___x_5770_;
goto v_reusejp_5784_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v_snd_5628_);
v___x_5785_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5784_;
}
v_reusejp_5784_:
{
lean_object* v___x_5787_; 
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 1, v___x_5785_);
lean_ctor_set(v___x_5765_, 0, v_fst_5623_);
v___x_5787_ = v___x_5765_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5785_);
v___x_5787_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5789_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v___x_5787_);
lean_ctor_set(v___x_5630_, 0, v___x_5783_);
v___x_5789_ = v___x_5630_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v___x_5783_);
lean_ctor_set(v_reuseFailAlloc_5793_, 1, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5791_; 
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 0, v___x_5789_);
v___x_5791_ = v___x_5779_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5789_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5806_; 
lean_del_object(v___x_5770_);
lean_dec(v_snd_5768_);
lean_del_object(v___x_5765_);
lean_dec_ref_known(v_snd_5628_, 1);
lean_del_object(v___x_5759_);
lean_del_object(v___x_5630_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
v_a_5799_ = lean_ctor_get(v___x_5777_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5801_ = v___x_5777_;
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5777_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5804_; 
if (v_isShared_5802_ == 0)
{
v___x_5804_ = v___x_5801_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_a_5799_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
else
{
lean_object* v_a_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5814_; 
lean_del_object(v___x_5770_);
lean_dec(v_snd_5768_);
lean_del_object(v___x_5765_);
lean_dec_ref_known(v_snd_5628_, 1);
lean_del_object(v___x_5759_);
lean_del_object(v___x_5630_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
lean_dec(v___x_5600_);
v_a_5807_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5809_ = v___x_5775_;
v_isShared_5810_ = v_isSharedCheck_5814_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_a_5807_);
lean_dec(v___x_5775_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5814_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v___x_5812_; 
if (v_isShared_5810_ == 0)
{
v___x_5812_ = v___x_5809_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_a_5807_);
v___x_5812_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
return v___x_5812_;
}
}
}
}
else
{
lean_object* v_a_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5822_; 
lean_del_object(v___x_5770_);
lean_dec(v_snd_5768_);
lean_dec(v_fst_5767_);
lean_del_object(v___x_5765_);
lean_dec_ref_known(v_snd_5628_, 1);
lean_del_object(v___x_5759_);
lean_del_object(v___x_5630_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
lean_dec(v___x_5600_);
v_a_5815_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5817_ = v___x_5773_;
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_a_5815_);
lean_dec(v___x_5773_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v___x_5820_; 
if (v_isShared_5818_ == 0)
{
v___x_5820_ = v___x_5817_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_a_5815_);
v___x_5820_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
return v___x_5820_;
}
}
}
}
else
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5830_; 
lean_del_object(v___x_5770_);
lean_dec(v_snd_5768_);
lean_dec(v_fst_5767_);
lean_del_object(v___x_5765_);
lean_dec_ref_known(v_snd_5628_, 1);
lean_del_object(v___x_5759_);
lean_del_object(v___x_5630_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
lean_dec(v___x_5600_);
v_a_5823_ = lean_ctor_get(v___x_5772_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5772_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5825_ = v___x_5772_;
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5772_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5828_; 
if (v_isShared_5826_ == 0)
{
v___x_5828_ = v___x_5825_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5823_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
}
}
}
else
{
if (v_stopAtFirstFailure_5601_ == 0)
{
lean_object* v_gs_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5839_; 
lean_del_object(v___x_5636_);
v_gs_5835_ = lean_ctor_get(v_a_5634_, 0);
lean_inc(v_gs_5835_);
lean_dec_ref_known(v_a_5634_, 1);
v___x_5836_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(v___x_5602_, v_gs_5835_);
v___x_5837_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_5627_, v___x_5836_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v___x_5837_);
v___x_5839_ = v___x_5630_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v___x_5837_);
lean_ctor_set(v_reuseFailAlloc_5847_, 1, v_snd_5628_);
v___x_5839_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
lean_object* v___x_5841_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5839_);
v___x_5841_ = v___x_5625_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5846_, 1, v___x_5839_);
v___x_5841_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
lean_object* v___x_5843_; 
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 1, v___x_5841_);
lean_ctor_set(v___x_5618_, 0, v___x_5632_);
v___x_5843_ = v___x_5618_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v___x_5632_);
lean_ctor_set(v_reuseFailAlloc_5845_, 1, v___x_5841_);
v___x_5843_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
v_as_x27_5603_ = v_tail_5622_;
v_b_5604_ = v___x_5843_;
goto _start;
}
}
}
}
else
{
lean_object* v_gs_5848_; lean_object* v___x_5850_; uint8_t v_isShared_5851_; uint8_t v_isSharedCheck_5869_; 
lean_dec(v___x_5600_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v_gs_5848_ = lean_ctor_get(v_a_5634_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v_a_5634_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5850_ = v_a_5634_;
v_isShared_5851_ = v_isSharedCheck_5869_;
goto v_resetjp_5849_;
}
else
{
lean_inc(v_gs_5848_);
lean_dec(v_a_5634_);
v___x_5850_ = lean_box(0);
v_isShared_5851_ = v_isSharedCheck_5869_;
goto v_resetjp_5849_;
}
v_resetjp_5849_:
{
lean_object* v___x_5852_; lean_object* v___x_5854_; 
v___x_5852_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(v___x_5602_, v_gs_5848_);
if (v_isShared_5851_ == 0)
{
lean_ctor_set(v___x_5850_, 0, v___x_5852_);
v___x_5854_ = v___x_5850_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5855_; lean_object* v___x_5857_; 
v___x_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5855_, 0, v___x_5854_);
if (v_isShared_5631_ == 0)
{
v___x_5857_ = v___x_5630_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5867_, 1, v_snd_5628_);
v___x_5857_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
lean_object* v___x_5859_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5857_);
v___x_5859_ = v___x_5625_;
goto v_reusejp_5858_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5866_, 1, v___x_5857_);
v___x_5859_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5858_;
}
v_reusejp_5858_:
{
lean_object* v___x_5861_; 
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 1, v___x_5859_);
lean_ctor_set(v___x_5618_, 0, v___x_5855_);
v___x_5861_ = v___x_5618_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v___x_5855_);
lean_ctor_set(v_reuseFailAlloc_5865_, 1, v___x_5859_);
v___x_5861_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
lean_object* v___x_5863_; 
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 0, v___x_5861_);
v___x_5863_ = v___x_5636_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v___x_5861_);
v___x_5863_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
return v___x_5863_;
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
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_del_object(v___x_5630_);
lean_dec(v_snd_5628_);
lean_dec(v_fst_5627_);
lean_del_object(v___x_5625_);
lean_dec(v_fst_5623_);
lean_del_object(v___x_5618_);
lean_dec(v___x_5600_);
lean_dec_ref(v_goal_5598_);
lean_dec(v_a_5597_);
lean_dec_ref(v_kp_5596_);
v_a_5871_ = lean_ctor_get(v___x_5633_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5633_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5633_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5633_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_kp_5884_ = _args[0];
lean_object* v_a_5885_ = _args[1];
lean_object* v_goal_5886_ = _args[2];
lean_object* v_snd_5887_ = _args[3];
lean_object* v___x_5888_ = _args[4];
lean_object* v_stopAtFirstFailure_5889_ = _args[5];
lean_object* v___x_5890_ = _args[6];
lean_object* v_as_x27_5891_ = _args[7];
lean_object* v_b_5892_ = _args[8];
lean_object* v___y_5893_ = _args[9];
lean_object* v___y_5894_ = _args[10];
lean_object* v___y_5895_ = _args[11];
lean_object* v___y_5896_ = _args[12];
lean_object* v___y_5897_ = _args[13];
lean_object* v___y_5898_ = _args[14];
lean_object* v___y_5899_ = _args[15];
lean_object* v___y_5900_ = _args[16];
lean_object* v___y_5901_ = _args[17];
lean_object* v___y_5902_ = _args[18];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5903_; lean_object* v_res_5904_; 
v_stopAtFirstFailure_boxed_5903_ = lean_unbox(v_stopAtFirstFailure_5889_);
v_res_5904_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_kp_5884_, v_a_5885_, v_goal_5886_, v_snd_5887_, v___x_5888_, v_stopAtFirstFailure_boxed_5903_, v___x_5890_, v_as_x27_5891_, v_b_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
lean_dec(v___y_5901_);
lean_dec_ref(v___y_5900_);
lean_dec(v___y_5899_);
lean_dec_ref(v___y_5898_);
lean_dec(v___y_5897_);
lean_dec_ref(v___y_5896_);
lean_dec(v___y_5895_);
lean_dec_ref(v___y_5894_);
lean_dec(v___y_5893_);
lean_dec(v_as_x27_5891_);
lean_dec_ref(v___x_5890_);
lean_dec_ref(v_snd_5887_);
return v_res_5904_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v___x_5905_, lean_object* v_c_5906_, lean_object* v___x_5907_, lean_object* v___x_5908_, lean_object* v___x_5909_, uint64_t v_a_5910_, uint8_t v_isRec_5911_, lean_object* v_a_5912_, lean_object* v_a_5913_){
_start:
{
if (lean_obj_tag(v_a_5912_) == 0)
{
lean_object* v___x_5914_; 
lean_dec_ref(v___x_5909_);
lean_dec(v___x_5908_);
lean_dec_ref(v___x_5907_);
lean_dec_ref(v___x_5905_);
v___x_5914_ = lean_array_to_list(v_a_5913_);
return v___x_5914_;
}
else
{
lean_object* v_split_5915_; lean_object* v_head_5916_; lean_object* v_tail_5917_; lean_object* v___x_5919_; uint8_t v_isShared_5920_; uint8_t v_isSharedCheck_5976_; 
v_split_5915_ = lean_ctor_get(v___x_5905_, 15);
lean_inc_ref(v_split_5915_);
v_head_5916_ = lean_ctor_get(v_a_5912_, 0);
v_tail_5917_ = lean_ctor_get(v_a_5912_, 1);
v_isSharedCheck_5976_ = !lean_is_exclusive(v_a_5912_);
if (v_isSharedCheck_5976_ == 0)
{
v___x_5919_ = v_a_5912_;
v_isShared_5920_ = v_isSharedCheck_5976_;
goto v_resetjp_5918_;
}
else
{
lean_inc(v_tail_5917_);
lean_inc(v_head_5916_);
lean_dec(v_a_5912_);
v___x_5919_ = lean_box(0);
v_isShared_5920_ = v_isSharedCheck_5976_;
goto v_resetjp_5918_;
}
v_resetjp_5918_:
{
lean_object* v_nextDeclIdx_5921_; lean_object* v_enodeMap_5922_; lean_object* v_exprs_5923_; lean_object* v_parents_5924_; lean_object* v_congrTable_5925_; lean_object* v_appMap_5926_; lean_object* v_indicesFound_5927_; lean_object* v_toProcess_5928_; lean_object* v_internalizing_5929_; uint8_t v_inconsistent_5930_; lean_object* v_nextIdx_5931_; lean_object* v_newRawFacts_5932_; lean_object* v_facts_5933_; lean_object* v_extThms_5934_; lean_object* v_ematch_5935_; lean_object* v_inj_5936_; lean_object* v_clean_5937_; lean_object* v_sstates_5938_; uint64_t v_introBase_5939_; lean_object* v_numIntros_5940_; lean_object* v_num_5941_; lean_object* v_candidates_5942_; lean_object* v_added_5943_; lean_object* v_resolved_5944_; lean_object* v_trace_5945_; lean_object* v_lookaheads_5946_; lean_object* v_argPosMap_5947_; lean_object* v_argsAt_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5975_; 
v_nextDeclIdx_5921_ = lean_ctor_get(v___x_5905_, 0);
v_enodeMap_5922_ = lean_ctor_get(v___x_5905_, 1);
v_exprs_5923_ = lean_ctor_get(v___x_5905_, 2);
v_parents_5924_ = lean_ctor_get(v___x_5905_, 3);
v_congrTable_5925_ = lean_ctor_get(v___x_5905_, 4);
v_appMap_5926_ = lean_ctor_get(v___x_5905_, 5);
v_indicesFound_5927_ = lean_ctor_get(v___x_5905_, 6);
v_toProcess_5928_ = lean_ctor_get(v___x_5905_, 7);
v_internalizing_5929_ = lean_ctor_get(v___x_5905_, 8);
v_inconsistent_5930_ = lean_ctor_get_uint8(v___x_5905_, sizeof(void*)*20 + 8);
v_nextIdx_5931_ = lean_ctor_get(v___x_5905_, 9);
v_newRawFacts_5932_ = lean_ctor_get(v___x_5905_, 10);
v_facts_5933_ = lean_ctor_get(v___x_5905_, 11);
v_extThms_5934_ = lean_ctor_get(v___x_5905_, 12);
v_ematch_5935_ = lean_ctor_get(v___x_5905_, 13);
v_inj_5936_ = lean_ctor_get(v___x_5905_, 14);
v_clean_5937_ = lean_ctor_get(v___x_5905_, 16);
v_sstates_5938_ = lean_ctor_get(v___x_5905_, 17);
v_introBase_5939_ = lean_ctor_get_uint64(v___x_5905_, sizeof(void*)*20);
v_numIntros_5940_ = lean_ctor_get(v___x_5905_, 19);
v_num_5941_ = lean_ctor_get(v_split_5915_, 0);
v_candidates_5942_ = lean_ctor_get(v_split_5915_, 1);
v_added_5943_ = lean_ctor_get(v_split_5915_, 2);
v_resolved_5944_ = lean_ctor_get(v_split_5915_, 3);
v_trace_5945_ = lean_ctor_get(v_split_5915_, 4);
v_lookaheads_5946_ = lean_ctor_get(v_split_5915_, 5);
v_argPosMap_5947_ = lean_ctor_get(v_split_5915_, 6);
v_argsAt_5948_ = lean_ctor_get(v_split_5915_, 7);
v_isSharedCheck_5975_ = !lean_is_exclusive(v_split_5915_);
if (v_isSharedCheck_5975_ == 0)
{
v___x_5950_ = v_split_5915_;
v_isShared_5951_ = v_isSharedCheck_5975_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_argsAt_5948_);
lean_inc(v_argPosMap_5947_);
lean_inc(v_lookaheads_5946_);
lean_inc(v_trace_5945_);
lean_inc(v_resolved_5944_);
lean_inc(v_added_5943_);
lean_inc(v_candidates_5942_);
lean_inc(v_num_5941_);
lean_dec(v_split_5915_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5975_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5952_; lean_object* v___y_5954_; lean_object* v___x_5973_; uint8_t v___x_5974_; 
v___x_5952_ = lean_array_get_size(v_a_5913_);
v___x_5973_ = lean_unsigned_to_nat(0u);
v___x_5974_ = lean_nat_dec_lt(v___x_5973_, v___x_5952_);
if (v___x_5974_ == 0)
{
if (v_isRec_5911_ == 0)
{
v___y_5954_ = v_num_5941_;
goto v___jp_5953_;
}
else
{
goto v___jp_5970_;
}
}
else
{
goto v___jp_5970_;
}
v___jp_5953_:
{
lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5958_; 
v___x_5955_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5906_);
lean_inc(v___x_5908_);
lean_inc_ref(v___x_5907_);
v___x_5956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5907_);
lean_ctor_set(v___x_5956_, 1, v___x_5952_);
lean_ctor_set(v___x_5956_, 2, v___x_5908_);
lean_ctor_set(v___x_5956_, 3, v___x_5955_);
if (v_isShared_5920_ == 0)
{
lean_ctor_set(v___x_5919_, 1, v_trace_5945_);
lean_ctor_set(v___x_5919_, 0, v___x_5956_);
v___x_5958_ = v___x_5919_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v___x_5956_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v_trace_5945_);
v___x_5958_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
lean_object* v___x_5960_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 4, v___x_5958_);
lean_ctor_set(v___x_5950_, 0, v___y_5954_);
v___x_5960_ = v___x_5950_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v___y_5954_);
lean_ctor_set(v_reuseFailAlloc_5968_, 1, v_candidates_5942_);
lean_ctor_set(v_reuseFailAlloc_5968_, 2, v_added_5943_);
lean_ctor_set(v_reuseFailAlloc_5968_, 3, v_resolved_5944_);
lean_ctor_set(v_reuseFailAlloc_5968_, 4, v___x_5958_);
lean_ctor_set(v_reuseFailAlloc_5968_, 5, v_lookaheads_5946_);
lean_ctor_set(v_reuseFailAlloc_5968_, 6, v_argPosMap_5947_);
lean_ctor_set(v_reuseFailAlloc_5968_, 7, v_argsAt_5948_);
v___x_5960_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
lean_object* v___x_5961_; lean_object* v___x_5962_; uint64_t v___x_5963_; uint64_t v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
lean_inc(v_numIntros_5940_);
lean_inc_ref(v___x_5909_);
lean_inc_ref(v_sstates_5938_);
lean_inc_ref(v_clean_5937_);
lean_inc_ref(v_inj_5936_);
lean_inc_ref(v_ematch_5935_);
lean_inc_ref(v_extThms_5934_);
lean_inc_ref(v_facts_5933_);
lean_inc_ref(v_newRawFacts_5932_);
lean_inc(v_nextIdx_5931_);
lean_inc_ref(v_internalizing_5929_);
lean_inc_ref(v_toProcess_5928_);
lean_inc_ref(v_indicesFound_5927_);
lean_inc_ref(v_appMap_5926_);
lean_inc_ref(v_congrTable_5925_);
lean_inc_ref(v_parents_5924_);
lean_inc_ref(v_exprs_5923_);
lean_inc_ref(v_enodeMap_5922_);
lean_inc(v_nextDeclIdx_5921_);
v___x_5961_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v___x_5961_, 0, v_nextDeclIdx_5921_);
lean_ctor_set(v___x_5961_, 1, v_enodeMap_5922_);
lean_ctor_set(v___x_5961_, 2, v_exprs_5923_);
lean_ctor_set(v___x_5961_, 3, v_parents_5924_);
lean_ctor_set(v___x_5961_, 4, v_congrTable_5925_);
lean_ctor_set(v___x_5961_, 5, v_appMap_5926_);
lean_ctor_set(v___x_5961_, 6, v_indicesFound_5927_);
lean_ctor_set(v___x_5961_, 7, v_toProcess_5928_);
lean_ctor_set(v___x_5961_, 8, v_internalizing_5929_);
lean_ctor_set(v___x_5961_, 9, v_nextIdx_5931_);
lean_ctor_set(v___x_5961_, 10, v_newRawFacts_5932_);
lean_ctor_set(v___x_5961_, 11, v_facts_5933_);
lean_ctor_set(v___x_5961_, 12, v_extThms_5934_);
lean_ctor_set(v___x_5961_, 13, v_ematch_5935_);
lean_ctor_set(v___x_5961_, 14, v_inj_5936_);
lean_ctor_set(v___x_5961_, 15, v___x_5960_);
lean_ctor_set(v___x_5961_, 16, v_clean_5937_);
lean_ctor_set(v___x_5961_, 17, v_sstates_5938_);
lean_ctor_set(v___x_5961_, 18, v___x_5909_);
lean_ctor_set(v___x_5961_, 19, v_numIntros_5940_);
lean_ctor_set_uint8(v___x_5961_, sizeof(void*)*20 + 8, v_inconsistent_5930_);
lean_ctor_set_uint64(v___x_5961_, sizeof(void*)*20, v_introBase_5939_);
v___x_5962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_ctor_set(v___x_5962_, 1, v_head_5916_);
v___x_5963_ = lean_uint64_of_nat(v___x_5952_);
v___x_5964_ = lean_uint64_mix_hash(v_a_5910_, v___x_5963_);
v___x_5965_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_5962_, v___x_5964_);
v___x_5966_ = lean_array_push(v_a_5913_, v___x_5965_);
v_a_5912_ = v_tail_5917_;
v_a_5913_ = v___x_5966_;
goto _start;
}
}
}
v___jp_5970_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5971_ = lean_unsigned_to_nat(1u);
v___x_5972_ = lean_nat_add(v_num_5941_, v___x_5971_);
lean_dec(v_num_5941_);
v___y_5954_ = v___x_5972_;
goto v___jp_5953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object* v___x_5977_, lean_object* v_c_5978_, lean_object* v___x_5979_, lean_object* v___x_5980_, lean_object* v___x_5981_, lean_object* v_a_5982_, lean_object* v_isRec_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_){
_start:
{
uint64_t v_a_104238__boxed_5986_; uint8_t v_isRec_boxed_5987_; lean_object* v_res_5988_; 
v_a_104238__boxed_5986_ = lean_unbox_uint64(v_a_5982_);
lean_dec_ref(v_a_5982_);
v_isRec_boxed_5987_ = lean_unbox(v_isRec_5983_);
v_res_5988_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v___x_5977_, v_c_5978_, v___x_5979_, v___x_5980_, v___x_5981_, v_a_104238__boxed_5986_, v_isRec_boxed_5987_, v_a_5984_, v_a_5985_);
lean_dec_ref(v_c_5978_);
return v_res_5988_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__6(void){
_start:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; 
v___x_6004_ = lean_box(0);
v___x_6005_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5));
v___x_6006_ = l_Lean_mkConst(v___x_6005_, v___x_6004_);
return v___x_6006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object* v_goal_6007_, lean_object* v_c_6008_, lean_object* v_numCases_6009_, uint8_t v_isRec_6010_, lean_object* v_candidates_x3f_6011_, lean_object* v_kp_6012_, uint8_t v_stopAtFirstFailure_6013_, uint8_t v_compress_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
lean_object* v___x_6025_; 
v___x_6025_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_6016_);
if (lean_obj_tag(v___x_6025_) == 0)
{
lean_object* v_a_6026_; uint8_t v_trace_6027_; lean_object* v___x_6028_; 
v_a_6026_ = lean_ctor_get(v___x_6025_, 0);
lean_inc(v_a_6026_);
lean_dec_ref_known(v___x_6025_, 1);
v_trace_6027_ = lean_ctor_get_uint8(v_a_6026_, sizeof(void*)*17);
lean_dec(v_a_6026_);
v___x_6028_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v___y_6016_, v___y_6017_, v___y_6021_, v___y_6023_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v_a_6029_; lean_object* v___x_6030_; 
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
lean_inc(v_a_6029_);
lean_dec_ref_known(v___x_6028_, 1);
lean_inc_ref(v_goal_6007_);
v___x_6030_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_6007_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6030_) == 0)
{
lean_object* v_a_6031_; lean_object* v_mvarId_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___f_6035_; lean_object* v___x_6036_; lean_object* v___f_6037_; lean_object* v___x_6038_; 
v_a_6031_ = lean_ctor_get(v___x_6030_, 0);
lean_inc_n(v_a_6031_, 2);
lean_dec_ref_known(v___x_6030_, 1);
v_mvarId_6032_ = lean_ctor_get(v_goal_6007_, 1);
v___x_6033_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6008_);
v___x_6034_ = lean_box(v_isRec_6010_);
lean_inc_ref_n(v_c_6008_, 2);
lean_inc_ref(v___x_6033_);
v___f_6035_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6035_, 0, v___x_6033_);
lean_closure_set(v___f_6035_, 1, v_c_6008_);
lean_closure_set(v___f_6035_, 2, v_a_6031_);
lean_closure_set(v___f_6035_, 3, v_numCases_6009_);
lean_closure_set(v___f_6035_, 4, v___x_6034_);
v___x_6036_ = lean_box(v_trace_6027_);
lean_inc_ref(v_goal_6007_);
v___f_6037_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_6037_, 0, v_goal_6007_);
lean_closure_set(v___f_6037_, 1, v___x_6036_);
lean_closure_set(v___f_6037_, 2, v___f_6035_);
lean_closure_set(v___f_6037_, 3, v_c_6008_);
lean_closure_set(v___f_6037_, 4, v_candidates_x3f_6011_);
lean_inc(v_mvarId_6032_);
v___x_6038_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6032_, v___f_6037_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; lean_object* v_fst_6040_; lean_object* v_snd_6041_; lean_object* v_toGoalState_6042_; lean_object* v_fst_6043_; lean_object* v_snd_6044_; lean_object* v___x_6046_; uint8_t v_isShared_6047_; uint8_t v_isSharedCheck_6181_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
lean_inc(v_a_6039_);
lean_dec_ref_known(v___x_6038_, 1);
v_fst_6040_ = lean_ctor_get(v_a_6039_, 0);
lean_inc(v_fst_6040_);
v_snd_6041_ = lean_ctor_get(v_a_6039_, 1);
lean_inc(v_snd_6041_);
lean_dec(v_a_6039_);
v_toGoalState_6042_ = lean_ctor_get(v_snd_6041_, 0);
v_fst_6043_ = lean_ctor_get(v_fst_6040_, 0);
v_snd_6044_ = lean_ctor_get(v_fst_6040_, 1);
v_isSharedCheck_6181_ = !lean_is_exclusive(v_fst_6040_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6046_ = v_fst_6040_;
v_isShared_6047_ = v_isSharedCheck_6181_;
goto v_resetjp_6045_;
}
else
{
lean_inc(v_snd_6044_);
lean_inc(v_fst_6043_);
lean_dec(v_fst_6040_);
v___x_6046_ = lean_box(0);
v_isShared_6047_ = v_isSharedCheck_6181_;
goto v_resetjp_6045_;
}
v_resetjp_6045_:
{
lean_object* v_mvarId_6048_; lean_object* v_goalStack_6049_; lean_object* v___x_6050_; lean_object* v___x_6052_; 
v_mvarId_6048_ = lean_ctor_get(v_snd_6041_, 1);
lean_inc_n(v_mvarId_6048_, 2);
v_goalStack_6049_ = lean_ctor_get(v_toGoalState_6042_, 18);
v___x_6050_ = l_List_lengthTR___redArg(v_fst_6043_);
lean_inc_ref(v_toGoalState_6042_);
if (v_isShared_6047_ == 0)
{
lean_ctor_set(v___x_6046_, 1, v_toGoalState_6042_);
lean_ctor_set(v___x_6046_, 0, v_mvarId_6048_);
v___x_6052_ = v___x_6046_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_mvarId_6048_);
lean_ctor_set(v_reuseFailAlloc_6180_, 1, v_toGoalState_6042_);
v___x_6052_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
lean_inc_ref(v_goalStack_6049_);
v___x_6053_ = lean_array_push(v_goalStack_6049_, v___x_6052_);
lean_inc_ref(v_c_6008_);
v___x_6054_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_6054_, 0, v_c_6008_);
lean_inc(v_mvarId_6048_);
v___x_6055_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6048_, v___x_6054_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6055_) == 0)
{
lean_object* v_a_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; uint64_t v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; 
v_a_6056_ = lean_ctor_get(v___x_6055_, 0);
lean_inc(v_a_6056_);
lean_dec_ref_known(v___x_6055_, 1);
v___x_6057_ = lean_unsigned_to_nat(0u);
v___x_6058_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0));
v___x_6059_ = lean_unbox_uint64(v_a_6056_);
lean_dec(v_a_6056_);
lean_inc_ref(v_toGoalState_6042_);
v___x_6060_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_toGoalState_6042_, v_c_6008_, v___x_6033_, v___x_6050_, v___x_6053_, v___x_6059_, v_isRec_6010_, v_fst_6043_, v___x_6058_);
lean_dec_ref(v_c_6008_);
v___x_6061_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3));
lean_inc(v_mvarId_6048_);
v___x_6062_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_kp_6012_, v_a_6029_, v_goal_6007_, v_snd_6041_, v_mvarId_6048_, v_stopAtFirstFailure_6013_, v_goalStack_6049_, v___x_6060_, v___x_6061_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
lean_dec(v___x_6060_);
if (lean_obj_tag(v___x_6062_) == 0)
{
lean_object* v_a_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6163_; 
v_a_6063_ = lean_ctor_get(v___x_6062_, 0);
v_isSharedCheck_6163_ = !lean_is_exclusive(v___x_6062_);
if (v_isSharedCheck_6163_ == 0)
{
v___x_6065_ = v___x_6062_;
v_isShared_6066_ = v_isSharedCheck_6163_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_a_6063_);
lean_dec(v___x_6062_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6163_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v_fst_6067_; 
v_fst_6067_ = lean_ctor_get(v_a_6063_, 0);
if (lean_obj_tag(v_fst_6067_) == 0)
{
lean_object* v_snd_6068_; lean_object* v_snd_6069_; lean_object* v_fst_6070_; lean_object* v_fst_6071_; lean_object* v___y_6073_; lean_object* v___y_6074_; lean_object* v___x_6121_; 
v_snd_6068_ = lean_ctor_get(v_a_6063_, 1);
lean_inc(v_snd_6068_);
lean_dec(v_a_6063_);
v_snd_6069_ = lean_ctor_get(v_snd_6068_, 1);
lean_inc(v_snd_6069_);
v_fst_6070_ = lean_ctor_get(v_snd_6068_, 0);
lean_inc(v_fst_6070_);
lean_dec(v_snd_6068_);
v_fst_6071_ = lean_ctor_get(v_snd_6069_, 0);
lean_inc(v_fst_6071_);
lean_dec(v_snd_6069_);
v___x_6121_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_6041_, v___y_6017_);
lean_dec(v_snd_6041_);
if (lean_obj_tag(v___x_6121_) == 0)
{
lean_object* v_a_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v_a_6125_; lean_object* v___x_6126_; 
v_a_6122_ = lean_ctor_get(v___x_6121_, 0);
lean_inc(v_a_6122_);
lean_dec_ref_known(v___x_6121_, 1);
v___x_6123_ = l_Lean_mkMVar(v_a_6031_);
v___x_6124_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v___x_6123_, v___y_6021_);
v_a_6125_ = lean_ctor_get(v___x_6124_, 0);
lean_inc(v_a_6125_);
lean_dec_ref(v___x_6124_);
v___x_6126_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_6122_, v_a_6125_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6126_) == 0)
{
lean_object* v_a_6127_; lean_object* v___x_6128_; 
v_a_6127_ = lean_ctor_get(v___x_6126_, 0);
lean_inc(v_a_6127_);
lean_dec_ref_known(v___x_6126_, 1);
lean_inc(v_mvarId_6048_);
v___x_6128_ = l_Lean_MVarId_getType(v_mvarId_6048_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6128_) == 0)
{
lean_object* v_a_6129_; uint8_t v___x_6130_; 
v_a_6129_ = lean_ctor_get(v___x_6128_, 0);
lean_inc(v_a_6129_);
lean_dec_ref_known(v___x_6128_, 1);
v___x_6130_ = l_Lean_Expr_isFalse(v_a_6129_);
lean_dec(v_a_6129_);
if (v___x_6130_ == 0)
{
lean_object* v___x_6131_; 
v___x_6131_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_6048_, v_a_6127_, v___y_6021_);
lean_dec_ref(v___x_6131_);
v___y_6073_ = v___y_6022_;
v___y_6074_ = v___y_6023_;
goto v___jp_6072_;
}
else
{
lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; 
v___x_6132_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__6, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__6_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__6);
v___x_6133_ = l_Lean_Meta_mkExpectedPropHint(v_a_6127_, v___x_6132_);
v___x_6134_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_6048_, v___x_6133_, v___y_6021_);
lean_dec_ref(v___x_6134_);
v___y_6073_ = v___y_6022_;
v___y_6074_ = v___y_6023_;
goto v___jp_6072_;
}
}
else
{
lean_object* v_a_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6142_; 
lean_dec(v_a_6127_);
lean_dec(v_fst_6071_);
lean_dec(v_fst_6070_);
lean_del_object(v___x_6065_);
lean_dec(v_mvarId_6048_);
lean_dec(v_snd_6044_);
v_a_6135_ = lean_ctor_get(v___x_6128_, 0);
v_isSharedCheck_6142_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6142_ == 0)
{
v___x_6137_ = v___x_6128_;
v_isShared_6138_ = v_isSharedCheck_6142_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_a_6135_);
lean_dec(v___x_6128_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6142_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v___x_6140_; 
if (v_isShared_6138_ == 0)
{
v___x_6140_ = v___x_6137_;
goto v_reusejp_6139_;
}
else
{
lean_object* v_reuseFailAlloc_6141_; 
v_reuseFailAlloc_6141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6141_, 0, v_a_6135_);
v___x_6140_ = v_reuseFailAlloc_6141_;
goto v_reusejp_6139_;
}
v_reusejp_6139_:
{
return v___x_6140_;
}
}
}
}
else
{
lean_object* v_a_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6150_; 
lean_dec(v_fst_6071_);
lean_dec(v_fst_6070_);
lean_del_object(v___x_6065_);
lean_dec(v_mvarId_6048_);
lean_dec(v_snd_6044_);
v_a_6143_ = lean_ctor_get(v___x_6126_, 0);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6126_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6145_ = v___x_6126_;
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_a_6143_);
lean_dec(v___x_6126_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6149_; 
v_reuseFailAlloc_6149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
v___x_6148_ = v_reuseFailAlloc_6149_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
return v___x_6148_;
}
}
}
}
else
{
lean_object* v_a_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6158_; 
lean_dec(v_fst_6071_);
lean_dec(v_fst_6070_);
lean_del_object(v___x_6065_);
lean_dec(v_mvarId_6048_);
lean_dec(v_snd_6044_);
lean_dec(v_a_6031_);
v_a_6151_ = lean_ctor_get(v___x_6121_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_6121_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_6153_ = v___x_6121_;
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_a_6151_);
lean_dec(v___x_6121_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6156_; 
if (v_isShared_6154_ == 0)
{
v___x_6156_ = v___x_6153_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_a_6151_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
v___jp_6072_:
{
lean_object* v___x_6075_; uint8_t v___x_6076_; 
v___x_6075_ = lean_array_get_size(v_fst_6071_);
v___x_6076_ = lean_nat_dec_eq(v___x_6075_, v___x_6057_);
if (v___x_6076_ == 0)
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6080_; 
lean_dec(v_fst_6070_);
lean_dec(v_snd_6044_);
v___x_6077_ = lean_array_to_list(v_fst_6071_);
v___x_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 0, v___x_6078_);
v___x_6080_ = v___x_6065_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6078_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
}
}
else
{
lean_dec(v_fst_6071_);
if (lean_obj_tag(v_snd_6044_) == 1)
{
lean_object* v_val_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6116_; 
lean_del_object(v___x_6065_);
v_val_6082_ = lean_ctor_get(v_snd_6044_, 0);
v_isSharedCheck_6116_ = !lean_is_exclusive(v_snd_6044_);
if (v_isSharedCheck_6116_ == 0)
{
v___x_6084_ = v_snd_6044_;
v_isShared_6085_ = v_isSharedCheck_6116_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_val_6082_);
lean_dec(v_snd_6044_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6116_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6086_; 
v___x_6086_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_6082_, v___y_6073_);
lean_dec(v_val_6082_);
if (lean_obj_tag(v___x_6086_) == 0)
{
lean_object* v_a_6087_; lean_object* v___x_6088_; 
v_a_6087_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_a_6087_);
lean_dec_ref_known(v___x_6086_, 1);
v___x_6088_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_6087_, v_fst_6070_, v_compress_6014_, v___y_6073_, v___y_6074_);
if (lean_obj_tag(v___x_6088_) == 0)
{
lean_object* v_a_6089_; lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6099_; 
v_a_6089_ = lean_ctor_get(v___x_6088_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6091_ = v___x_6088_;
v_isShared_6092_ = v_isSharedCheck_6099_;
goto v_resetjp_6090_;
}
else
{
lean_inc(v_a_6089_);
lean_dec(v___x_6088_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6099_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
lean_object* v___x_6094_; 
if (v_isShared_6085_ == 0)
{
lean_ctor_set_tag(v___x_6084_, 0);
lean_ctor_set(v___x_6084_, 0, v_a_6089_);
v___x_6094_ = v___x_6084_;
goto v_reusejp_6093_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6089_);
v___x_6094_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6093_;
}
v_reusejp_6093_:
{
lean_object* v___x_6096_; 
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 0, v___x_6094_);
v___x_6096_ = v___x_6091_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v___x_6094_);
v___x_6096_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
return v___x_6096_;
}
}
}
}
else
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6107_; 
lean_del_object(v___x_6084_);
v_a_6100_ = lean_ctor_get(v___x_6088_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6102_ = v___x_6088_;
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6088_);
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
else
{
lean_object* v_a_6108_; lean_object* v___x_6110_; uint8_t v_isShared_6111_; uint8_t v_isSharedCheck_6115_; 
lean_del_object(v___x_6084_);
lean_dec(v_fst_6070_);
v_a_6108_ = lean_ctor_get(v___x_6086_, 0);
v_isSharedCheck_6115_ = !lean_is_exclusive(v___x_6086_);
if (v_isSharedCheck_6115_ == 0)
{
v___x_6110_ = v___x_6086_;
v_isShared_6111_ = v_isSharedCheck_6115_;
goto v_resetjp_6109_;
}
else
{
lean_inc(v_a_6108_);
lean_dec(v___x_6086_);
v___x_6110_ = lean_box(0);
v_isShared_6111_ = v_isSharedCheck_6115_;
goto v_resetjp_6109_;
}
v_resetjp_6109_:
{
lean_object* v___x_6113_; 
if (v_isShared_6111_ == 0)
{
v___x_6113_ = v___x_6110_;
goto v_reusejp_6112_;
}
else
{
lean_object* v_reuseFailAlloc_6114_; 
v_reuseFailAlloc_6114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6114_, 0, v_a_6108_);
v___x_6113_ = v_reuseFailAlloc_6114_;
goto v_reusejp_6112_;
}
v_reusejp_6112_:
{
return v___x_6113_;
}
}
}
}
}
else
{
lean_object* v___x_6117_; lean_object* v___x_6119_; 
lean_dec(v_fst_6070_);
lean_dec(v_snd_6044_);
v___x_6117_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4));
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 0, v___x_6117_);
v___x_6119_ = v___x_6065_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6120_; 
v_reuseFailAlloc_6120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6120_, 0, v___x_6117_);
v___x_6119_ = v_reuseFailAlloc_6120_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
return v___x_6119_;
}
}
}
}
}
else
{
lean_object* v_val_6159_; lean_object* v___x_6161_; 
lean_inc_ref(v_fst_6067_);
lean_dec(v_a_6063_);
lean_dec(v_mvarId_6048_);
lean_dec(v_snd_6044_);
lean_dec(v_snd_6041_);
lean_dec(v_a_6031_);
v_val_6159_ = lean_ctor_get(v_fst_6067_, 0);
lean_inc(v_val_6159_);
lean_dec_ref_known(v_fst_6067_, 1);
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 0, v_val_6159_);
v___x_6161_ = v___x_6065_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6162_; 
v_reuseFailAlloc_6162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6162_, 0, v_val_6159_);
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
else
{
lean_object* v_a_6164_; lean_object* v___x_6166_; uint8_t v_isShared_6167_; uint8_t v_isSharedCheck_6171_; 
lean_dec(v_mvarId_6048_);
lean_dec(v_snd_6044_);
lean_dec(v_snd_6041_);
lean_dec(v_a_6031_);
v_a_6164_ = lean_ctor_get(v___x_6062_, 0);
v_isSharedCheck_6171_ = !lean_is_exclusive(v___x_6062_);
if (v_isSharedCheck_6171_ == 0)
{
v___x_6166_ = v___x_6062_;
v_isShared_6167_ = v_isSharedCheck_6171_;
goto v_resetjp_6165_;
}
else
{
lean_inc(v_a_6164_);
lean_dec(v___x_6062_);
v___x_6166_ = lean_box(0);
v_isShared_6167_ = v_isSharedCheck_6171_;
goto v_resetjp_6165_;
}
v_resetjp_6165_:
{
lean_object* v___x_6169_; 
if (v_isShared_6167_ == 0)
{
v___x_6169_ = v___x_6166_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_a_6164_);
v___x_6169_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
return v___x_6169_;
}
}
}
}
else
{
lean_object* v_a_6172_; lean_object* v___x_6174_; uint8_t v_isShared_6175_; uint8_t v_isSharedCheck_6179_; 
lean_dec_ref(v___x_6053_);
lean_dec(v___x_6050_);
lean_dec(v_mvarId_6048_);
lean_dec(v_snd_6044_);
lean_dec(v_fst_6043_);
lean_dec(v_snd_6041_);
lean_dec_ref(v___x_6033_);
lean_dec(v_a_6031_);
lean_dec(v_a_6029_);
lean_dec_ref(v_kp_6012_);
lean_dec_ref(v_c_6008_);
lean_dec_ref(v_goal_6007_);
v_a_6172_ = lean_ctor_get(v___x_6055_, 0);
v_isSharedCheck_6179_ = !lean_is_exclusive(v___x_6055_);
if (v_isSharedCheck_6179_ == 0)
{
v___x_6174_ = v___x_6055_;
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
else
{
lean_inc(v_a_6172_);
lean_dec(v___x_6055_);
v___x_6174_ = lean_box(0);
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
v_resetjp_6173_:
{
lean_object* v___x_6177_; 
if (v_isShared_6175_ == 0)
{
v___x_6177_ = v___x_6174_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6178_; 
v_reuseFailAlloc_6178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_a_6172_);
v___x_6177_ = v_reuseFailAlloc_6178_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
return v___x_6177_;
}
}
}
}
}
}
else
{
lean_object* v_a_6182_; lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6189_; 
lean_dec_ref(v___x_6033_);
lean_dec(v_a_6031_);
lean_dec(v_a_6029_);
lean_dec_ref(v_kp_6012_);
lean_dec_ref(v_c_6008_);
lean_dec_ref(v_goal_6007_);
v_a_6182_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6189_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6189_ == 0)
{
v___x_6184_ = v___x_6038_;
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
else
{
lean_inc(v_a_6182_);
lean_dec(v___x_6038_);
v___x_6184_ = lean_box(0);
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
v_resetjp_6183_:
{
lean_object* v___x_6187_; 
if (v_isShared_6185_ == 0)
{
v___x_6187_ = v___x_6184_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6188_; 
v_reuseFailAlloc_6188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
v___x_6187_ = v_reuseFailAlloc_6188_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
return v___x_6187_;
}
}
}
}
else
{
lean_object* v_a_6190_; lean_object* v___x_6192_; uint8_t v_isShared_6193_; uint8_t v_isSharedCheck_6197_; 
lean_dec(v_a_6029_);
lean_dec_ref(v_kp_6012_);
lean_dec(v_candidates_x3f_6011_);
lean_dec(v_numCases_6009_);
lean_dec_ref(v_c_6008_);
lean_dec_ref(v_goal_6007_);
v_a_6190_ = lean_ctor_get(v___x_6030_, 0);
v_isSharedCheck_6197_ = !lean_is_exclusive(v___x_6030_);
if (v_isSharedCheck_6197_ == 0)
{
v___x_6192_ = v___x_6030_;
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
else
{
lean_inc(v_a_6190_);
lean_dec(v___x_6030_);
v___x_6192_ = lean_box(0);
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
v_resetjp_6191_:
{
lean_object* v___x_6195_; 
if (v_isShared_6193_ == 0)
{
v___x_6195_ = v___x_6192_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6196_; 
v_reuseFailAlloc_6196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_a_6190_);
v___x_6195_ = v_reuseFailAlloc_6196_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
return v___x_6195_;
}
}
}
}
else
{
lean_object* v_a_6198_; lean_object* v___x_6200_; uint8_t v_isShared_6201_; uint8_t v_isSharedCheck_6205_; 
lean_dec_ref(v_kp_6012_);
lean_dec(v_candidates_x3f_6011_);
lean_dec(v_numCases_6009_);
lean_dec_ref(v_c_6008_);
lean_dec_ref(v_goal_6007_);
v_a_6198_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6205_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6205_ == 0)
{
v___x_6200_ = v___x_6028_;
v_isShared_6201_ = v_isSharedCheck_6205_;
goto v_resetjp_6199_;
}
else
{
lean_inc(v_a_6198_);
lean_dec(v___x_6028_);
v___x_6200_ = lean_box(0);
v_isShared_6201_ = v_isSharedCheck_6205_;
goto v_resetjp_6199_;
}
v_resetjp_6199_:
{
lean_object* v___x_6203_; 
if (v_isShared_6201_ == 0)
{
v___x_6203_ = v___x_6200_;
goto v_reusejp_6202_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v_a_6198_);
v___x_6203_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6202_;
}
v_reusejp_6202_:
{
return v___x_6203_;
}
}
}
}
else
{
lean_object* v_a_6206_; lean_object* v___x_6208_; uint8_t v_isShared_6209_; uint8_t v_isSharedCheck_6213_; 
lean_dec_ref(v_kp_6012_);
lean_dec(v_candidates_x3f_6011_);
lean_dec(v_numCases_6009_);
lean_dec_ref(v_c_6008_);
lean_dec_ref(v_goal_6007_);
v_a_6206_ = lean_ctor_get(v___x_6025_, 0);
v_isSharedCheck_6213_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6213_ == 0)
{
v___x_6208_ = v___x_6025_;
v_isShared_6209_ = v_isSharedCheck_6213_;
goto v_resetjp_6207_;
}
else
{
lean_inc(v_a_6206_);
lean_dec(v___x_6025_);
v___x_6208_ = lean_box(0);
v_isShared_6209_ = v_isSharedCheck_6213_;
goto v_resetjp_6207_;
}
v_resetjp_6207_:
{
lean_object* v___x_6211_; 
if (v_isShared_6209_ == 0)
{
v___x_6211_ = v___x_6208_;
goto v_reusejp_6210_;
}
else
{
lean_object* v_reuseFailAlloc_6212_; 
v_reuseFailAlloc_6212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6212_, 0, v_a_6206_);
v___x_6211_ = v_reuseFailAlloc_6212_;
goto v_reusejp_6210_;
}
v_reusejp_6210_:
{
return v___x_6211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_goal_6214_ = _args[0];
lean_object* v_c_6215_ = _args[1];
lean_object* v_numCases_6216_ = _args[2];
lean_object* v_isRec_6217_ = _args[3];
lean_object* v_candidates_x3f_6218_ = _args[4];
lean_object* v_kp_6219_ = _args[5];
lean_object* v_stopAtFirstFailure_6220_ = _args[6];
lean_object* v_compress_6221_ = _args[7];
lean_object* v___y_6222_ = _args[8];
lean_object* v___y_6223_ = _args[9];
lean_object* v___y_6224_ = _args[10];
lean_object* v___y_6225_ = _args[11];
lean_object* v___y_6226_ = _args[12];
lean_object* v___y_6227_ = _args[13];
lean_object* v___y_6228_ = _args[14];
lean_object* v___y_6229_ = _args[15];
lean_object* v___y_6230_ = _args[16];
lean_object* v___y_6231_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6232_; uint8_t v_stopAtFirstFailure_boxed_6233_; uint8_t v_compress_boxed_6234_; lean_object* v_res_6235_; 
v_isRec_boxed_6232_ = lean_unbox(v_isRec_6217_);
v_stopAtFirstFailure_boxed_6233_ = lean_unbox(v_stopAtFirstFailure_6220_);
v_compress_boxed_6234_ = lean_unbox(v_compress_6221_);
v_res_6235_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(v_goal_6214_, v_c_6215_, v_numCases_6216_, v_isRec_boxed_6232_, v_candidates_x3f_6218_, v_kp_6219_, v_stopAtFirstFailure_boxed_6233_, v_compress_boxed_6234_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v___y_6226_);
lean_dec_ref(v___y_6225_);
lean_dec(v___y_6224_);
lean_dec_ref(v___y_6223_);
lean_dec(v___y_6222_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_6236_, lean_object* v_numCases_6237_, uint8_t v_isRec_6238_, uint8_t v_stopAtFirstFailure_6239_, uint8_t v_compress_6240_, lean_object* v_candidates_x3f_6241_, lean_object* v_goal_6242_, lean_object* v_kp_6243_, lean_object* v_a_6244_, lean_object* v_a_6245_, lean_object* v_a_6246_, lean_object* v_a_6247_, lean_object* v_a_6248_, lean_object* v_a_6249_, lean_object* v_a_6250_, lean_object* v_a_6251_, lean_object* v_a_6252_){
_start:
{
lean_object* v___x_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___f_6257_; lean_object* v___x_6258_; 
v___x_6254_ = lean_box(v_isRec_6238_);
v___x_6255_ = lean_box(v_stopAtFirstFailure_6239_);
v___x_6256_ = lean_box(v_compress_6240_);
lean_inc_ref(v_goal_6242_);
v___f_6257_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed), 18, 8);
lean_closure_set(v___f_6257_, 0, v_goal_6242_);
lean_closure_set(v___f_6257_, 1, v_c_6236_);
lean_closure_set(v___f_6257_, 2, v_numCases_6237_);
lean_closure_set(v___f_6257_, 3, v___x_6254_);
lean_closure_set(v___f_6257_, 4, v_candidates_x3f_6241_);
lean_closure_set(v___f_6257_, 5, v_kp_6243_);
lean_closure_set(v___f_6257_, 6, v___x_6255_);
lean_closure_set(v___f_6257_, 7, v___x_6256_);
v___x_6258_ = l_Lean_Meta_Grind_withHoistedDecls___redArg(v_goal_6242_, v___f_6257_, v_a_6244_, v_a_6245_, v_a_6246_, v_a_6247_, v_a_6248_, v_a_6249_, v_a_6250_, v_a_6251_, v_a_6252_);
return v___x_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6259_ = _args[0];
lean_object* v_numCases_6260_ = _args[1];
lean_object* v_isRec_6261_ = _args[2];
lean_object* v_stopAtFirstFailure_6262_ = _args[3];
lean_object* v_compress_6263_ = _args[4];
lean_object* v_candidates_x3f_6264_ = _args[5];
lean_object* v_goal_6265_ = _args[6];
lean_object* v_kp_6266_ = _args[7];
lean_object* v_a_6267_ = _args[8];
lean_object* v_a_6268_ = _args[9];
lean_object* v_a_6269_ = _args[10];
lean_object* v_a_6270_ = _args[11];
lean_object* v_a_6271_ = _args[12];
lean_object* v_a_6272_ = _args[13];
lean_object* v_a_6273_ = _args[14];
lean_object* v_a_6274_ = _args[15];
lean_object* v_a_6275_ = _args[16];
lean_object* v_a_6276_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6277_; uint8_t v_stopAtFirstFailure_boxed_6278_; uint8_t v_compress_boxed_6279_; lean_object* v_res_6280_; 
v_isRec_boxed_6277_ = lean_unbox(v_isRec_6261_);
v_stopAtFirstFailure_boxed_6278_ = lean_unbox(v_stopAtFirstFailure_6262_);
v_compress_boxed_6279_ = lean_unbox(v_compress_6263_);
v_res_6280_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6259_, v_numCases_6260_, v_isRec_boxed_6277_, v_stopAtFirstFailure_boxed_6278_, v_compress_boxed_6279_, v_candidates_x3f_6264_, v_goal_6265_, v_kp_6266_, v_a_6267_, v_a_6268_, v_a_6269_, v_a_6270_, v_a_6271_, v_a_6272_, v_a_6273_, v_a_6274_, v_a_6275_);
lean_dec(v_a_6275_);
lean_dec_ref(v_a_6274_);
lean_dec(v_a_6273_);
lean_dec_ref(v_a_6272_);
lean_dec(v_a_6271_);
lean_dec_ref(v_a_6270_);
lean_dec(v_a_6269_);
lean_dec_ref(v_a_6268_);
lean_dec(v_a_6267_);
return v_res_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6281_, lean_object* v_numCases_6282_, uint8_t v_isRec_6283_, uint8_t v_stopAtFirstFailure_6284_, uint8_t v_compress_6285_, lean_object* v_candidates_x3f_6286_, lean_object* v_goal_6287_, lean_object* v_x_6288_, lean_object* v_kp_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_, lean_object* v_a_6296_, lean_object* v_a_6297_, lean_object* v_a_6298_){
_start:
{
lean_object* v___x_6300_; 
v___x_6300_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6281_, v_numCases_6282_, v_isRec_6283_, v_stopAtFirstFailure_6284_, v_compress_6285_, v_candidates_x3f_6286_, v_goal_6287_, v_kp_6289_, v_a_6290_, v_a_6291_, v_a_6292_, v_a_6293_, v_a_6294_, v_a_6295_, v_a_6296_, v_a_6297_, v_a_6298_);
return v___x_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6301_ = _args[0];
lean_object* v_numCases_6302_ = _args[1];
lean_object* v_isRec_6303_ = _args[2];
lean_object* v_stopAtFirstFailure_6304_ = _args[3];
lean_object* v_compress_6305_ = _args[4];
lean_object* v_candidates_x3f_6306_ = _args[5];
lean_object* v_goal_6307_ = _args[6];
lean_object* v_x_6308_ = _args[7];
lean_object* v_kp_6309_ = _args[8];
lean_object* v_a_6310_ = _args[9];
lean_object* v_a_6311_ = _args[10];
lean_object* v_a_6312_ = _args[11];
lean_object* v_a_6313_ = _args[12];
lean_object* v_a_6314_ = _args[13];
lean_object* v_a_6315_ = _args[14];
lean_object* v_a_6316_ = _args[15];
lean_object* v_a_6317_ = _args[16];
lean_object* v_a_6318_ = _args[17];
lean_object* v_a_6319_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6320_; uint8_t v_stopAtFirstFailure_boxed_6321_; uint8_t v_compress_boxed_6322_; lean_object* v_res_6323_; 
v_isRec_boxed_6320_ = lean_unbox(v_isRec_6303_);
v_stopAtFirstFailure_boxed_6321_ = lean_unbox(v_stopAtFirstFailure_6304_);
v_compress_boxed_6322_ = lean_unbox(v_compress_6305_);
v_res_6323_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6301_, v_numCases_6302_, v_isRec_boxed_6320_, v_stopAtFirstFailure_boxed_6321_, v_compress_boxed_6322_, v_candidates_x3f_6306_, v_goal_6307_, v_x_6308_, v_kp_6309_, v_a_6310_, v_a_6311_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
lean_dec(v_a_6318_);
lean_dec_ref(v_a_6317_);
lean_dec(v_a_6316_);
lean_dec_ref(v_a_6315_);
lean_dec(v_a_6314_);
lean_dec_ref(v_a_6313_);
lean_dec(v_a_6312_);
lean_dec_ref(v_a_6311_);
lean_dec(v_a_6310_);
lean_dec_ref(v_x_6308_);
return v_res_6323_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_kp_6324_, lean_object* v_a_6325_, lean_object* v_goal_6326_, lean_object* v_snd_6327_, lean_object* v___x_6328_, uint8_t v_stopAtFirstFailure_6329_, lean_object* v___x_6330_, lean_object* v_as_6331_, lean_object* v_as_x27_6332_, lean_object* v_b_6333_, lean_object* v_a_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_){
_start:
{
lean_object* v___x_6345_; 
v___x_6345_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_kp_6324_, v_a_6325_, v_goal_6326_, v_snd_6327_, v___x_6328_, v_stopAtFirstFailure_6329_, v___x_6330_, v_as_x27_6332_, v_b_6333_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object** _args){
lean_object* v_kp_6346_ = _args[0];
lean_object* v_a_6347_ = _args[1];
lean_object* v_goal_6348_ = _args[2];
lean_object* v_snd_6349_ = _args[3];
lean_object* v___x_6350_ = _args[4];
lean_object* v_stopAtFirstFailure_6351_ = _args[5];
lean_object* v___x_6352_ = _args[6];
lean_object* v_as_6353_ = _args[7];
lean_object* v_as_x27_6354_ = _args[8];
lean_object* v_b_6355_ = _args[9];
lean_object* v_a_6356_ = _args[10];
lean_object* v___y_6357_ = _args[11];
lean_object* v___y_6358_ = _args[12];
lean_object* v___y_6359_ = _args[13];
lean_object* v___y_6360_ = _args[14];
lean_object* v___y_6361_ = _args[15];
lean_object* v___y_6362_ = _args[16];
lean_object* v___y_6363_ = _args[17];
lean_object* v___y_6364_ = _args[18];
lean_object* v___y_6365_ = _args[19];
lean_object* v___y_6366_ = _args[20];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6367_; lean_object* v_res_6368_; 
v_stopAtFirstFailure_boxed_6367_ = lean_unbox(v_stopAtFirstFailure_6351_);
v_res_6368_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_kp_6346_, v_a_6347_, v_goal_6348_, v_snd_6349_, v___x_6350_, v_stopAtFirstFailure_boxed_6367_, v___x_6352_, v_as_6353_, v_as_x27_6354_, v_b_6355_, v_a_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_);
lean_dec(v___y_6365_);
lean_dec_ref(v___y_6364_);
lean_dec(v___y_6363_);
lean_dec_ref(v___y_6362_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec(v___y_6359_);
lean_dec_ref(v___y_6358_);
lean_dec(v___y_6357_);
lean_dec(v_as_x27_6354_);
lean_dec(v_as_6353_);
lean_dec_ref(v___x_6352_);
lean_dec_ref(v_snd_6349_);
return v_res_6368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6(lean_object* v_mvarId_6369_, lean_object* v_val_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_6369_, v_val_6370_, v___y_6377_);
return v___x_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___boxed(lean_object* v_mvarId_6382_, lean_object* v_val_6383_, lean_object* v___y_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_){
_start:
{
lean_object* v_res_6394_; 
v_res_6394_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6(v_mvarId_6382_, v_val_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_);
lean_dec(v___y_6392_);
lean_dec_ref(v___y_6391_);
lean_dec(v___y_6390_);
lean_dec_ref(v___y_6389_);
lean_dec(v___y_6388_);
lean_dec_ref(v___y_6387_);
lean_dec(v___y_6386_);
lean_dec_ref(v___y_6385_);
lean_dec(v___y_6384_);
return v_res_6394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6(lean_object* v_00_u03b2_6395_, lean_object* v_x_6396_, lean_object* v_x_6397_, lean_object* v_x_6398_){
_start:
{
lean_object* v___x_6399_; 
v___x_6399_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(v_x_6396_, v_x_6397_, v_x_6398_);
return v___x_6399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_6400_, lean_object* v_x_6401_, size_t v_x_6402_, size_t v_x_6403_, lean_object* v_x_6404_, lean_object* v_x_6405_){
_start:
{
lean_object* v___x_6406_; 
v___x_6406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_x_6401_, v_x_6402_, v_x_6403_, v_x_6404_, v_x_6405_);
return v___x_6406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___boxed(lean_object* v_00_u03b2_6407_, lean_object* v_x_6408_, lean_object* v_x_6409_, lean_object* v_x_6410_, lean_object* v_x_6411_, lean_object* v_x_6412_){
_start:
{
size_t v_x_104880__boxed_6413_; size_t v_x_104881__boxed_6414_; lean_object* v_res_6415_; 
v_x_104880__boxed_6413_ = lean_unbox_usize(v_x_6409_);
lean_dec(v_x_6409_);
v_x_104881__boxed_6414_ = lean_unbox_usize(v_x_6410_);
lean_dec(v_x_6410_);
v_res_6415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7(v_00_u03b2_6407_, v_x_6408_, v_x_104880__boxed_6413_, v_x_104881__boxed_6414_, v_x_6411_, v_x_6412_);
return v_res_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6416_, lean_object* v_n_6417_, lean_object* v_k_6418_, lean_object* v_v_6419_){
_start:
{
lean_object* v___x_6420_; 
v___x_6420_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(v_n_6417_, v_k_6418_, v_v_6419_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_6421_, size_t v_depth_6422_, lean_object* v_keys_6423_, lean_object* v_vals_6424_, lean_object* v_heq_6425_, lean_object* v_i_6426_, lean_object* v_entries_6427_){
_start:
{
lean_object* v___x_6428_; 
v___x_6428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(v_depth_6422_, v_keys_6423_, v_vals_6424_, v_i_6426_, v_entries_6427_);
return v___x_6428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_6429_, lean_object* v_depth_6430_, lean_object* v_keys_6431_, lean_object* v_vals_6432_, lean_object* v_heq_6433_, lean_object* v_i_6434_, lean_object* v_entries_6435_){
_start:
{
size_t v_depth_boxed_6436_; lean_object* v_res_6437_; 
v_depth_boxed_6436_ = lean_unbox_usize(v_depth_6430_);
lean_dec(v_depth_6430_);
v_res_6437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9(v_00_u03b2_6429_, v_depth_boxed_6436_, v_keys_6431_, v_vals_6432_, v_heq_6433_, v_i_6434_, v_entries_6435_);
lean_dec_ref(v_vals_6432_);
lean_dec_ref(v_keys_6431_);
return v_res_6437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_6438_, lean_object* v_x_6439_, lean_object* v_x_6440_, lean_object* v_x_6441_, lean_object* v_x_6442_){
_start:
{
lean_object* v___x_6443_; 
v___x_6443_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(v_x_6439_, v_x_6440_, v_x_6441_, v_x_6442_);
return v___x_6443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_){
_start:
{
lean_object* v___x_6457_; 
v___x_6457_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6444_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_, v___y_6455_);
return v___x_6457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_){
_start:
{
lean_object* v_res_6471_; 
v_res_6471_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
lean_dec(v___y_6469_);
lean_dec_ref(v___y_6468_);
lean_dec(v___y_6467_);
lean_dec_ref(v___y_6466_);
lean_dec(v___y_6465_);
lean_dec_ref(v___y_6464_);
lean_dec(v___y_6463_);
lean_dec_ref(v___y_6462_);
lean_dec(v___y_6461_);
lean_dec_ref(v___y_6459_);
return v_res_6471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_){
_start:
{
lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6483_ = lean_st_mk_ref(v_goal_6472_);
v___x_6484_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6483_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_);
if (lean_obj_tag(v___x_6484_) == 0)
{
lean_object* v_a_6485_; lean_object* v___x_6487_; uint8_t v_isShared_6488_; uint8_t v_isSharedCheck_6494_; 
v_a_6485_ = lean_ctor_get(v___x_6484_, 0);
v_isSharedCheck_6494_ = !lean_is_exclusive(v___x_6484_);
if (v_isSharedCheck_6494_ == 0)
{
v___x_6487_ = v___x_6484_;
v_isShared_6488_ = v_isSharedCheck_6494_;
goto v_resetjp_6486_;
}
else
{
lean_inc(v_a_6485_);
lean_dec(v___x_6484_);
v___x_6487_ = lean_box(0);
v_isShared_6488_ = v_isSharedCheck_6494_;
goto v_resetjp_6486_;
}
v_resetjp_6486_:
{
lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6492_; 
v___x_6489_ = lean_st_ref_get(v___x_6483_);
lean_dec(v___x_6483_);
v___x_6490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6490_, 0, v_a_6485_);
lean_ctor_set(v___x_6490_, 1, v___x_6489_);
if (v_isShared_6488_ == 0)
{
lean_ctor_set(v___x_6487_, 0, v___x_6490_);
v___x_6492_ = v___x_6487_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6493_; 
v_reuseFailAlloc_6493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6493_, 0, v___x_6490_);
v___x_6492_ = v_reuseFailAlloc_6493_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
return v___x_6492_;
}
}
}
else
{
lean_object* v_a_6495_; lean_object* v___x_6497_; uint8_t v_isShared_6498_; uint8_t v_isSharedCheck_6502_; 
lean_dec(v___x_6483_);
v_a_6495_ = lean_ctor_get(v___x_6484_, 0);
v_isSharedCheck_6502_ = !lean_is_exclusive(v___x_6484_);
if (v_isSharedCheck_6502_ == 0)
{
v___x_6497_ = v___x_6484_;
v_isShared_6498_ = v_isSharedCheck_6502_;
goto v_resetjp_6496_;
}
else
{
lean_inc(v_a_6495_);
lean_dec(v___x_6484_);
v___x_6497_ = lean_box(0);
v_isShared_6498_ = v_isSharedCheck_6502_;
goto v_resetjp_6496_;
}
v_resetjp_6496_:
{
lean_object* v___x_6500_; 
if (v_isShared_6498_ == 0)
{
v___x_6500_ = v___x_6497_;
goto v_reusejp_6499_;
}
else
{
lean_object* v_reuseFailAlloc_6501_; 
v_reuseFailAlloc_6501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6501_, 0, v_a_6495_);
v___x_6500_ = v_reuseFailAlloc_6501_;
goto v_reusejp_6499_;
}
v_reusejp_6499_:
{
return v___x_6500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_){
_start:
{
lean_object* v_res_6514_; 
v_res_6514_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6503_, v___y_6504_, v___y_6505_, v___y_6506_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_, v___y_6512_);
lean_dec(v___y_6512_);
lean_dec_ref(v___y_6511_);
lean_dec(v___y_6510_);
lean_dec_ref(v___y_6509_);
lean_dec(v___y_6508_);
lean_dec_ref(v___y_6507_);
lean_dec(v___y_6506_);
lean_dec_ref(v___y_6505_);
lean_dec(v___y_6504_);
return v_res_6514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6515_, lean_object* v___f_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_){
_start:
{
lean_object* v___x_6530_; lean_object* v___x_6531_; 
v___x_6530_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6530_, 0, v___y_6515_);
v___x_6531_ = l_Lean_Meta_Grind_Action_andThen(v___x_6530_, v___f_6516_, v___y_6517_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
return v___x_6531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6532_, lean_object* v___f_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_, lean_object* v___y_6545_, lean_object* v___y_6546_){
_start:
{
lean_object* v_res_6547_; 
v_res_6547_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6532_, v___f_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_, v___y_6544_, v___y_6545_);
lean_dec(v___y_6545_);
lean_dec_ref(v___y_6544_);
lean_dec(v___y_6543_);
lean_dec_ref(v___y_6542_);
lean_dec(v___y_6541_);
lean_dec_ref(v___y_6540_);
lean_dec(v___y_6539_);
lean_dec_ref(v___y_6538_);
lean_dec(v___y_6537_);
return v_res_6547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6549_, uint8_t v_compress_6550_, lean_object* v_goal_6551_, lean_object* v_kna_6552_, lean_object* v_kp_6553_, lean_object* v_a_6554_, lean_object* v_a_6555_, lean_object* v_a_6556_, lean_object* v_a_6557_, lean_object* v_a_6558_, lean_object* v_a_6559_, lean_object* v_a_6560_, lean_object* v_a_6561_, lean_object* v_a_6562_){
_start:
{
lean_object* v_toGoalState_6564_; lean_object* v_split_6565_; lean_object* v_mvarId_6566_; lean_object* v_candidates_6567_; lean_object* v___f_6568_; lean_object* v___f_6569_; lean_object* v___x_6570_; 
v_toGoalState_6564_ = lean_ctor_get(v_goal_6551_, 0);
v_split_6565_ = lean_ctor_get(v_toGoalState_6564_, 15);
v_mvarId_6566_ = lean_ctor_get(v_goal_6551_, 1);
lean_inc(v_mvarId_6566_);
v_candidates_6567_ = lean_ctor_get(v_split_6565_, 1);
lean_inc(v_candidates_6567_);
v___f_6568_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6569_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6569_, 0, v_goal_6551_);
v___x_6570_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6566_, v___f_6569_, v_a_6554_, v_a_6555_, v_a_6556_, v_a_6557_, v_a_6558_, v_a_6559_, v_a_6560_, v_a_6561_, v_a_6562_);
if (lean_obj_tag(v___x_6570_) == 0)
{
lean_object* v_a_6571_; lean_object* v_fst_6572_; 
v_a_6571_ = lean_ctor_get(v___x_6570_, 0);
lean_inc(v_a_6571_);
lean_dec_ref_known(v___x_6570_, 1);
v_fst_6572_ = lean_ctor_get(v_a_6571_, 0);
if (lean_obj_tag(v_fst_6572_) == 1)
{
lean_object* v_snd_6573_; lean_object* v_c_6574_; lean_object* v_numCases_6575_; uint8_t v_isRec_6576_; lean_object* v___y_6578_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; uint8_t v___x_6591_; 
lean_inc_ref(v_fst_6572_);
v_snd_6573_ = lean_ctor_get(v_a_6571_, 1);
lean_inc(v_snd_6573_);
lean_dec(v_a_6571_);
v_c_6574_ = lean_ctor_get(v_fst_6572_, 0);
lean_inc_ref(v_c_6574_);
v_numCases_6575_ = lean_ctor_get(v_fst_6572_, 1);
lean_inc(v_numCases_6575_);
v_isRec_6576_ = lean_ctor_get_uint8(v_fst_6572_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6572_, 2);
v___x_6586_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6574_);
v___x_6587_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6573_, v___x_6586_);
lean_dec_ref(v___x_6586_);
v___x_6588_ = lean_unsigned_to_nat(1u);
v___x_6591_ = lean_nat_dec_lt(v___x_6588_, v_numCases_6575_);
if (v___x_6591_ == 0)
{
if (v_isRec_6576_ == 0)
{
v___y_6578_ = v___x_6587_;
goto v___jp_6577_;
}
else
{
goto v___jp_6589_;
}
}
else
{
goto v___jp_6589_;
}
v___jp_6577_:
{
lean_object* v___f_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; 
v___f_6579_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6579_, 0, v___y_6578_);
lean_closure_set(v___f_6579_, 1, v___f_6568_);
v___x_6580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6580_, 0, v_candidates_6567_);
v___x_6581_ = lean_box(v_isRec_6576_);
v___x_6582_ = lean_box(v_stopAtFirstFailure_6549_);
v___x_6583_ = lean_box(v_compress_6550_);
v___x_6584_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6584_, 0, v_c_6574_);
lean_closure_set(v___x_6584_, 1, v_numCases_6575_);
lean_closure_set(v___x_6584_, 2, v___x_6581_);
lean_closure_set(v___x_6584_, 3, v___x_6582_);
lean_closure_set(v___x_6584_, 4, v___x_6583_);
lean_closure_set(v___x_6584_, 5, v___x_6580_);
v___x_6585_ = l_Lean_Meta_Grind_Action_andThen(v___x_6584_, v___f_6579_, v_snd_6573_, v_kna_6552_, v_kp_6553_, v_a_6554_, v_a_6555_, v_a_6556_, v_a_6557_, v_a_6558_, v_a_6559_, v_a_6560_, v_a_6561_, v_a_6562_);
return v___x_6585_;
}
v___jp_6589_:
{
lean_object* v___x_6590_; 
v___x_6590_ = lean_nat_add(v___x_6587_, v___x_6588_);
lean_dec(v___x_6587_);
v___y_6578_ = v___x_6590_;
goto v___jp_6577_;
}
}
else
{
lean_object* v_snd_6592_; lean_object* v___x_6593_; 
lean_dec(v_candidates_6567_);
lean_dec_ref(v_kp_6553_);
v_snd_6592_ = lean_ctor_get(v_a_6571_, 1);
lean_inc(v_snd_6592_);
lean_dec(v_a_6571_);
lean_inc(v_a_6562_);
lean_inc_ref(v_a_6561_);
lean_inc(v_a_6560_);
lean_inc_ref(v_a_6559_);
lean_inc(v_a_6558_);
lean_inc_ref(v_a_6557_);
lean_inc(v_a_6556_);
lean_inc_ref(v_a_6555_);
lean_inc(v_a_6554_);
v___x_6593_ = lean_apply_11(v_kna_6552_, v_snd_6592_, v_a_6554_, v_a_6555_, v_a_6556_, v_a_6557_, v_a_6558_, v_a_6559_, v_a_6560_, v_a_6561_, v_a_6562_, lean_box(0));
return v___x_6593_;
}
}
else
{
lean_object* v_a_6594_; lean_object* v___x_6596_; uint8_t v_isShared_6597_; uint8_t v_isSharedCheck_6601_; 
lean_dec(v_candidates_6567_);
lean_dec_ref(v_kp_6553_);
lean_dec_ref(v_kna_6552_);
v_a_6594_ = lean_ctor_get(v___x_6570_, 0);
v_isSharedCheck_6601_ = !lean_is_exclusive(v___x_6570_);
if (v_isSharedCheck_6601_ == 0)
{
v___x_6596_ = v___x_6570_;
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
else
{
lean_inc(v_a_6594_);
lean_dec(v___x_6570_);
v___x_6596_ = lean_box(0);
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
v_resetjp_6595_:
{
lean_object* v___x_6599_; 
if (v_isShared_6597_ == 0)
{
v___x_6599_ = v___x_6596_;
goto v_reusejp_6598_;
}
else
{
lean_object* v_reuseFailAlloc_6600_; 
v_reuseFailAlloc_6600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6600_, 0, v_a_6594_);
v___x_6599_ = v_reuseFailAlloc_6600_;
goto v_reusejp_6598_;
}
v_reusejp_6598_:
{
return v___x_6599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6602_, lean_object* v_compress_6603_, lean_object* v_goal_6604_, lean_object* v_kna_6605_, lean_object* v_kp_6606_, lean_object* v_a_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_, lean_object* v_a_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_, lean_object* v_a_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6617_; uint8_t v_compress_boxed_6618_; lean_object* v_res_6619_; 
v_stopAtFirstFailure_boxed_6617_ = lean_unbox(v_stopAtFirstFailure_6602_);
v_compress_boxed_6618_ = lean_unbox(v_compress_6603_);
v_res_6619_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6617_, v_compress_boxed_6618_, v_goal_6604_, v_kna_6605_, v_kp_6606_, v_a_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_, v_a_6614_, v_a_6615_);
lean_dec(v_a_6615_);
lean_dec_ref(v_a_6614_);
lean_dec(v_a_6613_);
lean_dec_ref(v_a_6612_);
lean_dec(v_a_6611_);
lean_dec_ref(v_a_6610_);
lean_dec(v_a_6609_);
lean_dec_ref(v_a_6608_);
lean_dec(v_a_6607_);
return v_res_6619_;
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
