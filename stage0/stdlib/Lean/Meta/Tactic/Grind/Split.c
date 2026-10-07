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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Goal_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", generation: "};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___y_64_ = v_isRec_58_;
goto v___jp_63_;
}
}
v___jp_63_:
{
if (v___y_64_ == 0)
{
return v___y_64_;
}
else
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
lean_object* v___y_151_; lean_object* v___x_177_; 
lean_inc_ref(v_c_142_);
v___x_177_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; uint8_t v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v___x_179_ = lean_unbox(v_a_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec_ref_known(v___x_177_, 1);
v___x_180_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
v___y_151_ = v___x_180_;
goto v___jp_150_;
}
else
{
lean_dec_ref(v_c_142_);
v___y_151_ = v___x_177_;
goto v___jp_150_;
}
}
else
{
lean_dec_ref(v_c_142_);
v___y_151_ = v___x_177_;
goto v___jp_150_;
}
v___jp_150_:
{
if (lean_obj_tag(v___y_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_168_; 
v_a_152_ = lean_ctor_get(v___y_151_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___y_151_);
if (v_isSharedCheck_168_ == 0)
{
v___x_154_ = v___y_151_;
v_isShared_155_ = v_isSharedCheck_168_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___y_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_168_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
uint8_t v___x_156_; 
v___x_156_ = lean_unbox(v_a_152_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; uint8_t v___x_160_; lean_object* v___x_162_; 
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_158_, 0, v___x_157_);
v___x_159_ = lean_unbox(v_a_152_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_159_);
v___x_160_ = lean_unbox(v_a_152_);
lean_dec(v_a_152_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1 + 1, v___x_160_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_158_);
v___x_162_ = v___x_154_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_158_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_a_152_);
v___x_164_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_164_);
v___x_166_ = v___x_154_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_169_ = lean_ctor_get(v___y_151_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___y_151_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___y_151_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___y_151_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object* v_c_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* v_c_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_190_, v_a_191_, v_a_195_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* v_c_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(v_c_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec(v_a_204_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* v_e_216_, lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___y_227_; lean_object* v___x_253_; 
lean_inc_ref(v_e_216_);
v___x_253_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_216_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; uint8_t v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v___x_255_ = lean_unbox(v_a_254_);
lean_dec(v_a_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_a_217_);
v___x_256_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_216_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_270_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_270_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_270_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_270_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; 
v___x_261_ = lean_unbox(v_a_257_);
lean_dec(v_a_257_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_box(1);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_266_);
v___x_268_ = v___x_259_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_271_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_256_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_256_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v___x_279_; 
lean_dec_ref(v_e_216_);
v___x_279_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_217_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; uint8_t v___x_281_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v___x_281_ = lean_unbox(v_a_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_dec_ref_known(v___x_279_, 1);
v___x_282_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
v___y_227_ = v___x_282_;
goto v___jp_226_;
}
else
{
lean_dec_ref(v_b_218_);
v___y_227_ = v___x_279_;
goto v___jp_226_;
}
}
else
{
lean_dec_ref(v_b_218_);
v___y_227_ = v___x_279_;
goto v___jp_226_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_a_217_);
lean_dec_ref(v_e_216_);
v_a_283_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_253_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_253_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
v___jp_226_:
{
if (lean_obj_tag(v___y_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_244_; 
v_a_228_ = lean_ctor_get(v___y_227_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___y_227_);
if (v_isSharedCheck_244_ == 0)
{
v___x_230_ = v___y_227_;
v_isShared_231_ = v_isSharedCheck_244_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___y_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_244_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; 
v___x_232_ = lean_unbox(v_a_228_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; uint8_t v___x_236_; lean_object* v___x_238_; 
v___x_233_ = lean_unsigned_to_nat(2u);
v___x_234_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_unbox(v_a_228_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_235_);
v___x_236_ = lean_unbox(v_a_228_);
lean_dec(v_a_228_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1 + 1, v___x_236_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_234_);
v___x_238_ = v___x_230_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_234_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_242_; 
lean_dec(v_a_228_);
v___x_240_ = lean_box(0);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_240_);
v___x_242_ = v___x_230_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___y_227_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___y_227_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___y_227_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___y_227_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_b_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_291_, v_a_292_, v_b_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* v_e_302_, lean_object* v_a_303_, lean_object* v_b_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_302_, v_a_303_, v_b_304_, v_a_305_, v_a_309_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* v_e_317_, lean_object* v_a_318_, lean_object* v_b_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(v_e_317_, v_a_318_, v_b_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec(v_a_320_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_b_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___y_343_; lean_object* v___x_369_; 
lean_inc_ref(v_e_332_);
v___x_369_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_332_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_402_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_402_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_402_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_402_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_unbox(v_a_370_);
lean_dec(v_a_370_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_del_object(v___x_372_);
v___x_375_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_332_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_389_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_389_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint8_t v___x_380_; 
v___x_380_ = lean_unbox(v_a_376_);
lean_dec(v_a_376_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_dec_ref(v_b_334_);
lean_dec_ref(v_a_333_);
v___x_381_ = lean_box(1);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
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
lean_object* v___x_385_; 
lean_del_object(v___x_378_);
v___x_385_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_333_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; uint8_t v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v___x_387_ = lean_unbox(v_a_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref_known(v___x_385_, 1);
v___x_388_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
v___y_343_ = v___x_388_;
goto v___jp_342_;
}
else
{
lean_dec_ref(v_b_334_);
v___y_343_ = v___x_385_;
goto v___jp_342_;
}
}
else
{
lean_dec_ref(v_b_334_);
v___y_343_ = v___x_385_;
goto v___jp_342_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_b_334_);
lean_dec_ref(v_a_333_);
v_a_390_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_375_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_375_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_dec_ref(v_b_334_);
lean_dec_ref(v_a_333_);
lean_dec_ref(v_e_332_);
v___x_398_ = lean_box(0);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_398_);
v___x_400_ = v___x_372_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
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
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_b_334_);
lean_dec_ref(v_a_333_);
lean_dec_ref(v_e_332_);
v_a_403_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_369_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_369_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
v___jp_342_:
{
if (lean_obj_tag(v___y_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_360_; 
v_a_344_ = lean_ctor_get(v___y_343_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___y_343_);
if (v_isSharedCheck_360_ == 0)
{
v___x_346_ = v___y_343_;
v_isShared_347_ = v_isSharedCheck_360_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___y_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_360_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___x_348_; 
v___x_348_ = lean_unbox(v_a_344_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; uint8_t v___x_352_; lean_object* v___x_354_; 
v___x_349_ = lean_unsigned_to_nat(2u);
v___x_350_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_350_, 0, v___x_349_);
v___x_351_ = lean_unbox(v_a_344_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*1, v___x_351_);
v___x_352_ = lean_unbox(v_a_344_);
lean_dec(v_a_344_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*1 + 1, v___x_352_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_350_);
v___x_354_ = v___x_346_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_350_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_a_344_);
v___x_356_ = lean_box(0);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_356_);
v___x_358_ = v___x_346_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v___y_343_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___y_343_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___y_343_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___y_343_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_b_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_411_, v_a_412_, v_b_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* v_e_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_422_, v_a_423_, v_b_424_, v_a_425_, v_a_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(v_e_437_, v_a_438_, v_b_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec(v_a_440_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* v_e_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___y_466_; lean_object* v___y_489_; lean_object* v___y_508_; lean_object* v___y_531_; lean_object* v___x_546_; 
lean_inc_ref(v_e_452_);
v___x_546_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_452_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; uint8_t v___x_548_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_452_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_563_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_563_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_unbox(v_a_550_);
lean_dec(v_a_550_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_557_; 
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
v___x_555_ = lean_box(1);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
lean_object* v___x_559_; 
lean_del_object(v___x_552_);
lean_inc_ref(v_a_453_);
v___x_559_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_453_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; uint8_t v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v___x_561_ = lean_unbox(v_a_560_);
if (v___x_561_ == 0)
{
v___y_489_ = v___x_559_;
goto v___jp_488_;
}
else
{
lean_object* v___x_562_; 
lean_dec_ref_known(v___x_559_, 1);
lean_inc_ref(v_b_454_);
v___x_562_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
v___y_489_ = v___x_562_;
goto v___jp_488_;
}
}
else
{
v___y_489_ = v___x_559_;
goto v___jp_488_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
v_a_564_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_549_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_549_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v___x_572_; 
lean_dec_ref(v_e_452_);
lean_inc_ref(v_a_453_);
v___x_572_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_453_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; uint8_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v___x_574_ = lean_unbox(v_a_573_);
if (v___x_574_ == 0)
{
v___y_531_ = v___x_572_;
goto v___jp_530_;
}
else
{
lean_object* v___x_575_; 
lean_dec_ref_known(v___x_572_, 1);
lean_inc_ref(v_b_454_);
v___x_575_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
v___y_531_ = v___x_575_;
goto v___jp_530_;
}
}
else
{
v___y_531_ = v___x_572_;
goto v___jp_530_;
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
lean_dec_ref(v_e_452_);
v_a_576_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_546_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_546_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
v___jp_462_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
v___jp_465_:
{
if (lean_obj_tag(v___y_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_479_; 
v_a_467_ = lean_ctor_get(v___y_466_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_466_);
if (v_isSharedCheck_479_ == 0)
{
v___x_469_ = v___y_466_;
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___y_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint8_t v___x_471_; 
v___x_471_ = lean_unbox(v_a_467_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; uint8_t v___x_475_; lean_object* v___x_477_; 
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_473_, 0, v___x_472_);
v___x_474_ = lean_unbox(v_a_467_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_474_);
v___x_475_ = lean_unbox(v_a_467_);
lean_dec(v_a_467_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1 + 1, v___x_475_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_473_);
v___x_477_ = v___x_469_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_473_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_del_object(v___x_469_);
lean_dec(v_a_467_);
goto v___jp_462_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_a_480_ = lean_ctor_get(v___y_466_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___y_466_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___y_466_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___y_466_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
v___jp_488_:
{
if (lean_obj_tag(v___y_489_) == 0)
{
lean_object* v_a_490_; uint8_t v___x_491_; 
v_a_490_ = lean_ctor_get(v___y_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___y_489_, 1);
v___x_491_ = lean_unbox(v_a_490_);
lean_dec(v_a_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_453_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; uint8_t v___x_494_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v___x_494_ = lean_unbox(v_a_493_);
if (v___x_494_ == 0)
{
lean_dec_ref(v_b_454_);
v___y_466_ = v___x_492_;
goto v___jp_465_;
}
else
{
lean_object* v___x_495_; 
lean_dec_ref_known(v___x_492_, 1);
v___x_495_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
v___y_466_ = v___x_495_;
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_b_454_);
v___y_466_ = v___x_492_;
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
goto v___jp_462_;
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
v_a_496_ = lean_ctor_get(v___y_489_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___y_489_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___y_489_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___y_489_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
v___jp_504_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_box(0);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
v___jp_507_:
{
if (lean_obj_tag(v___y_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_521_; 
v_a_509_ = lean_ctor_get(v___y_508_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_521_ == 0)
{
v___x_511_ = v___y_508_;
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___y_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint8_t v___x_513_; 
v___x_513_ = lean_unbox(v_a_509_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; uint8_t v___x_517_; lean_object* v___x_519_; 
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_unbox(v_a_509_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_516_);
v___x_517_ = lean_unbox(v_a_509_);
lean_dec(v_a_509_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1 + 1, v___x_517_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_515_);
v___x_519_ = v___x_511_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_515_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_del_object(v___x_511_);
lean_dec(v_a_509_);
goto v___jp_504_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___y_508_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___y_508_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___y_508_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
v___jp_530_:
{
if (lean_obj_tag(v___y_531_) == 0)
{
lean_object* v_a_532_; uint8_t v___x_533_; 
v_a_532_ = lean_ctor_get(v___y_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___y_531_, 1);
v___x_533_ = lean_unbox(v_a_532_);
lean_dec(v_a_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_453_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; uint8_t v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v___x_536_ = lean_unbox(v_a_535_);
if (v___x_536_ == 0)
{
lean_dec_ref(v_b_454_);
v___y_508_ = v___x_534_;
goto v___jp_507_;
}
else
{
lean_object* v___x_537_; 
lean_dec_ref_known(v___x_534_, 1);
v___x_537_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
v___y_508_ = v___x_537_;
goto v___jp_507_;
}
}
else
{
lean_dec_ref(v_b_454_);
v___y_508_ = v___x_534_;
goto v___jp_507_;
}
}
else
{
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
goto v___jp_504_;
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_b_454_);
lean_dec_ref(v_a_453_);
v_a_538_ = lean_ctor_get(v___y_531_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___y_531_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___y_531_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___y_531_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object* v_e_584_, lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_584_, v_a_585_, v_b_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* v_e_595_, lean_object* v_a_596_, lean_object* v_b_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_595_, v_a_596_, v_b_597_, v_a_598_, v_a_602_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* v_e_610_, lean_object* v_a_611_, lean_object* v_b_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(v_e_610_, v_a_611_, v_b_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec(v_a_613_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object* v_c_625_, uint8_t v___x_626_, uint8_t v_d_627_, lean_object* v_a_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
if (v_d_627_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_st_ref_get(v___y_630_);
v___x_642_ = l_Lean_Expr_isApp(v_a_628_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v___x_641_);
lean_dec_ref(v_a_628_);
lean_dec_ref(v_c_625_);
v___x_643_ = lean_box(v_d_627_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_Meta_Grind_Goal_isCongruent(v___x_641_, v_c_625_, v_a_628_);
lean_dec(v___x_641_);
v___x_646_ = lean_box(v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v_a_628_);
lean_dec_ref(v_c_625_);
v___x_648_ = lean_box(v___x_626_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* v_c_650_, lean_object* v___x_651_, lean_object* v_d_652_, lean_object* v_a_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v___x_7896__boxed_666_; uint8_t v_d_boxed_667_; lean_object* v_res_668_; 
v___x_7896__boxed_666_ = lean_unbox(v___x_651_);
v_d_boxed_667_ = lean_unbox(v_d_652_);
v_res_668_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_650_, v___x_7896__boxed_666_, v_d_boxed_667_, v_a_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec(v___y_655_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(lean_object* v_f_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_i_672_, lean_object* v_acc_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_get_size(v_keys_670_);
v___x_686_ = lean_nat_dec_lt(v_i_672_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec(v_i_672_);
lean_dec_ref(v_f_669_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_acc_673_);
return v___x_687_;
}
else
{
lean_object* v_k_688_; lean_object* v_v_689_; lean_object* v___x_690_; 
v_k_688_ = lean_array_fget_borrowed(v_keys_670_, v_i_672_);
v_v_689_ = lean_array_fget_borrowed(v_vals_671_, v_i_672_);
lean_inc_ref(v_f_669_);
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc(v___y_674_);
lean_inc(v_v_689_);
lean_inc(v_k_688_);
v___x_690_ = lean_apply_14(v_f_669_, v_acc_673_, v_k_688_, v_v_689_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, lean_box(0));
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_i_672_, v___x_692_);
lean_dec(v_i_672_);
v_i_672_ = v___x_693_;
v_acc_673_ = v_a_691_;
goto _start;
}
else
{
lean_dec(v_i_672_);
lean_dec_ref(v_f_669_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_695_, lean_object* v_keys_696_, lean_object* v_vals_697_, lean_object* v_i_698_, lean_object* v_acc_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_695_, v_keys_696_, v_vals_697_, v_i_698_, v_acc_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v_vals_697_);
lean_dec_ref(v_keys_696_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* v_f_712_, lean_object* v_as_713_, size_t v_i_714_, size_t v_stop_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_a_729_; lean_object* v___y_734_; uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_eq(v_i_714_, v_stop_715_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_array_uget_borrowed(v_as_713_, v_i_714_);
switch(lean_obj_tag(v___x_737_))
{
case 0:
{
lean_object* v_key_738_; lean_object* v_val_739_; lean_object* v___x_740_; 
v_key_738_ = lean_ctor_get(v___x_737_, 0);
v_val_739_ = lean_ctor_get(v___x_737_, 1);
lean_inc_ref(v_f_712_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc(v___y_717_);
lean_inc(v_val_739_);
lean_inc(v_key_738_);
v___x_740_ = lean_apply_14(v_f_712_, v_b_716_, v_key_738_, v_val_739_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, lean_box(0));
v___y_734_ = v___x_740_;
goto v___jp_733_;
}
case 1:
{
lean_object* v_node_741_; lean_object* v___x_742_; 
v_node_741_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_node_741_);
lean_inc_ref(v_f_712_);
v___x_742_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_712_, v_node_741_, v_b_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
v___y_734_ = v___x_742_;
goto v___jp_733_;
}
default: 
{
v_a_729_ = v_b_716_;
goto v___jp_728_;
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec_ref(v_f_712_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_b_716_);
return v___x_743_;
}
v___jp_728_:
{
size_t v___x_730_; size_t v___x_731_; 
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_714_, v___x_730_);
v_i_714_ = v___x_731_;
v_b_716_ = v_a_729_;
goto _start;
}
v___jp_733_:
{
if (lean_obj_tag(v___y_734_) == 0)
{
lean_object* v_a_735_; 
v_a_735_ = lean_ctor_get(v___y_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___y_734_, 1);
v_a_729_ = v_a_735_;
goto v___jp_728_;
}
else
{
lean_dec_ref(v_f_712_);
return v___y_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* v_f_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
if (lean_obj_tag(v_x_745_) == 0)
{
lean_object* v_es_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_771_; 
v_es_758_ = lean_ctor_get(v_x_745_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_745_);
if (v_isSharedCheck_771_ == 0)
{
v___x_760_ = v_x_745_;
v_isShared_761_ = v_isSharedCheck_771_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_es_758_);
lean_dec(v_x_745_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_771_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_array_get_size(v_es_758_);
v___x_764_ = lean_nat_dec_lt(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v_es_758_);
lean_dec_ref(v_f_744_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v_x_746_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_x_746_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; 
lean_del_object(v___x_760_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = lean_usize_of_nat(v___x_763_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_744_, v_es_758_, v___x_768_, v___x_769_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_es_758_);
return v___x_770_;
}
}
}
else
{
lean_object* v_ks_772_; lean_object* v_vs_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_ks_772_ = lean_ctor_get(v_x_745_, 0);
lean_inc_ref(v_ks_772_);
v_vs_773_ = lean_ctor_get(v_x_745_, 1);
lean_inc_ref(v_vs_773_);
lean_dec_ref_known(v_x_745_, 2);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_744_, v_ks_772_, v_vs_773_, v___x_774_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_vs_773_);
lean_dec_ref(v_ks_772_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_776_, v_x_777_, v_x_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_791_, lean_object* v_as_792_, lean_object* v_i_793_, lean_object* v_stop_794_, lean_object* v_b_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_i_boxed_807_; size_t v_stop_boxed_808_; lean_object* v_res_809_; 
v_i_boxed_807_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_stop_boxed_808_ = lean_unbox_usize(v_stop_794_);
lean_dec(v_stop_794_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_791_, v_as_792_, v_i_boxed_807_, v_stop_boxed_808_, v_b_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v_as_792_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* v_c_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_Expr_isApp(v_c_810_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref(v_c_810_);
v___x_823_ = lean_box(v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v_toGoalState_828_; lean_object* v_split_829_; lean_object* v_resolved_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_825_ = lean_box(v___x_822_);
v___f_826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 16, 2);
lean_closure_set(v___f_826_, 0, v_c_810_);
lean_closure_set(v___f_826_, 1, v___x_825_);
v___x_827_ = lean_st_ref_get(v_a_811_);
v_toGoalState_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_toGoalState_828_);
lean_dec(v___x_827_);
v_split_829_ = lean_ctor_get(v_toGoalState_828_, 14);
lean_inc_ref(v_split_829_);
lean_dec_ref(v_toGoalState_828_);
v_resolved_830_ = lean_ctor_get(v_split_829_, 3);
lean_inc_ref(v_resolved_830_);
lean_dec_ref(v_split_829_);
v___x_831_ = 0;
v___x_832_ = lean_box(v___x_831_);
v___x_833_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v___f_826_, v_resolved_830_, v___x_832_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object* v_c_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec(v_a_835_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* v_map_847_, lean_object* v_f_848_, lean_object* v_init_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_848_, v_map_847_, v_init_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* v_map_862_, lean_object* v_f_863_, lean_object* v_init_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_862_, v_f_863_, v_init_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v___y_865_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* v_00_u03c3_877_, lean_object* v_00_u03b2_878_, lean_object* v_map_879_, lean_object* v_f_880_, lean_object* v_init_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_880_, v_map_879_, v_init_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* v_00_u03c3_894_, lean_object* v_00_u03b2_895_, lean_object* v_map_896_, lean_object* v_f_897_, lean_object* v_init_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(v_00_u03c3_894_, v_00_u03b2_895_, v_map_896_, v_f_897_, v_init_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* v_00_u03c3_911_, lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_f_914_, lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_914_, v_x_915_, v_x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_929_ = _args[0];
lean_object* v_00_u03b1_930_ = _args[1];
lean_object* v_00_u03b2_931_ = _args[2];
lean_object* v_f_932_ = _args[3];
lean_object* v_x_933_ = _args[4];
lean_object* v_x_934_ = _args[5];
lean_object* v___y_935_ = _args[6];
lean_object* v___y_936_ = _args[7];
lean_object* v___y_937_ = _args[8];
lean_object* v___y_938_ = _args[9];
lean_object* v___y_939_ = _args[10];
lean_object* v___y_940_ = _args[11];
lean_object* v___y_941_ = _args[12];
lean_object* v___y_942_ = _args[13];
lean_object* v___y_943_ = _args[14];
lean_object* v___y_944_ = _args[15];
lean_object* v___y_945_ = _args[16];
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(v_00_u03c3_929_, v_00_u03b1_930_, v_00_u03b2_931_, v_f_932_, v_x_933_, v_x_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_947_, lean_object* v_00_u03b2_948_, lean_object* v_00_u03c3_949_, lean_object* v_f_950_, lean_object* v_as_951_, size_t v_i_952_, size_t v_stop_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_950_, v_as_951_, v_i_952_, v_stop_953_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_967_ = _args[0];
lean_object* v_00_u03b2_968_ = _args[1];
lean_object* v_00_u03c3_969_ = _args[2];
lean_object* v_f_970_ = _args[3];
lean_object* v_as_971_ = _args[4];
lean_object* v_i_972_ = _args[5];
lean_object* v_stop_973_ = _args[6];
lean_object* v_b_974_ = _args[7];
lean_object* v___y_975_ = _args[8];
lean_object* v___y_976_ = _args[9];
lean_object* v___y_977_ = _args[10];
lean_object* v___y_978_ = _args[11];
lean_object* v___y_979_ = _args[12];
lean_object* v___y_980_ = _args[13];
lean_object* v___y_981_ = _args[14];
lean_object* v___y_982_ = _args[15];
lean_object* v___y_983_ = _args[16];
lean_object* v___y_984_ = _args[17];
lean_object* v___y_985_ = _args[18];
_start:
{
size_t v_i_boxed_986_; size_t v_stop_boxed_987_; lean_object* v_res_988_; 
v_i_boxed_986_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_987_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(v_00_u03b1_967_, v_00_u03b2_968_, v_00_u03c3_969_, v_f_970_, v_as_971_, v_i_boxed_986_, v_stop_boxed_987_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v_as_971_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_989_, lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_f_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_heq_995_, lean_object* v_i_996_, lean_object* v_acc_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_992_, v_keys_993_, v_vals_994_, v_i_996_, v_acc_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_1010_ = _args[0];
lean_object* v_00_u03b1_1011_ = _args[1];
lean_object* v_00_u03b2_1012_ = _args[2];
lean_object* v_f_1013_ = _args[3];
lean_object* v_keys_1014_ = _args[4];
lean_object* v_vals_1015_ = _args[5];
lean_object* v_heq_1016_ = _args[6];
lean_object* v_i_1017_ = _args[7];
lean_object* v_acc_1018_ = _args[8];
lean_object* v___y_1019_ = _args[9];
lean_object* v___y_1020_ = _args[10];
lean_object* v___y_1021_ = _args[11];
lean_object* v___y_1022_ = _args[12];
lean_object* v___y_1023_ = _args[13];
lean_object* v___y_1024_ = _args[14];
lean_object* v___y_1025_ = _args[15];
lean_object* v___y_1026_ = _args[16];
lean_object* v___y_1027_ = _args[17];
lean_object* v___y_1028_ = _args[18];
lean_object* v___y_1029_ = _args[19];
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(v_00_u03c3_1010_, v_00_u03b1_1011_, v_00_u03b2_1012_, v_f_1013_, v_keys_1014_, v_vals_1015_, v_heq_1016_, v_i_1017_, v_acc_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v_vals_1015_);
lean_dec_ref(v_keys_1014_);
return v_res_1030_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1035_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
lean_ctor_set(v___x_1037_, 3, v___x_1036_);
lean_ctor_set(v___x_1037_, 4, v___x_1035_);
lean_ctor_set(v___x_1037_, 5, v___x_1035_);
lean_ctor_set(v___x_1037_, 6, v___x_1035_);
lean_ctor_set(v___x_1037_, 7, v___x_1035_);
lean_ctor_set(v___x_1037_, 8, v___x_1035_);
lean_ctor_set(v___x_1037_, 9, v___x_1035_);
lean_ctor_set(v___x_1037_, 10, v___x_1035_);
lean_ctor_set(v___x_1037_, 11, v___x_1034_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_unsigned_to_nat(32u);
v___x_1039_ = lean_mk_empty_array_with_capacity(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1041_ = ((size_t)5ULL);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_unsigned_to_nat(32u);
v___x_1044_ = lean_mk_empty_array_with_capacity(v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1046_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1044_);
lean_ctor_set(v___x_1046_, 2, v___x_1042_);
lean_ctor_set(v___x_1046_, 3, v___x_1042_);
lean_ctor_set_usize(v___x_1046_, 4, v___x_1041_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1047_ = lean_box(1);
v___x_1048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1048_);
lean_ctor_set(v___x_1050_, 2, v___x_1047_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_env_1078_; uint8_t v___x_1079_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_st_ref_get(v___y_1074_);
v_env_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_env_1078_);
lean_dec(v___x_1077_);
v___x_1079_ = l_Lean_Name_isAnonymous(v_declHint_1073_);
if (v___x_1079_ == 0)
{
uint8_t v_isExporting_1080_; 
v_isExporting_1080_ = lean_ctor_get_uint8(v_env_1078_, sizeof(void*)*13);
if (v_isExporting_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1073_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_msg_1072_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
lean_inc_ref(v_env_1078_);
v___x_1082_ = l_Lean_Environment_setExporting(v_env_1078_, v___x_1079_);
lean_inc(v_declHint_1073_);
lean_inc_ref(v___x_1082_);
v___x_1083_ = l_Lean_Environment_contains(v___x_1082_, v_declHint_1073_, v_isExporting_1080_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref(v___x_1082_);
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1073_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_msg_1072_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_c_1090_; lean_object* v___x_1091_; 
v___x_1085_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1087_ = l_Lean_Options_empty;
v___x_1088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1082_);
lean_ctor_set(v___x_1088_, 1, v___x_1085_);
lean_ctor_set(v___x_1088_, 2, v___x_1086_);
lean_ctor_set(v___x_1088_, 3, v___x_1087_);
lean_inc(v_declHint_1073_);
v___x_1089_ = l_Lean_MessageData_ofConstName(v_declHint_1073_, v___x_1079_);
v_c_1090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1090_, 0, v___x_1088_);
lean_ctor_set(v_c_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1078_, v_declHint_1073_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1073_);
v___x_1092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_c_1090_);
v___x_1094_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_MessageData_note(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_msg_1072_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1133_; 
v_val_1099_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1101_ = v___x_1091_;
v_isShared_1102_ = v_isSharedCheck_1133_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v___x_1091_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1133_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_mod_1105_; uint8_t v___x_1106_; 
v___x_1103_ = l_Lean_Environment_header(v_env_1078_);
lean_dec_ref(v_env_1078_);
v___x_1104_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1103_);
v_mod_1105_ = lean_array_get(v___x_1076_, v___x_1104_, v_val_1099_);
lean_dec(v_val_1099_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = l_Lean_isPrivateName(v_declHint_1073_);
lean_dec(v_declHint_1073_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v_c_1090_);
v___x_1109_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_MessageData_ofName(v_mod_1105_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_MessageData_note(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_msg_1072_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1116_);
v___x_1118_ = v___x_1101_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v_c_1090_);
v___x_1122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_MessageData_ofName(v_mod_1105_);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_MessageData_note(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_msg_1072_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1129_);
v___x_1131_ = v___x_1101_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1134_; 
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1073_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_msg_1072_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1135_, lean_object* v_declHint_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1135_, v_declHint_1136_, v___y_1137_);
lean_dec(v___y_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1140_, lean_object* v_declHint_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
v___x_1153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1140_, v_declHint_1141_, v___y_1151_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1158_ = l_Lean_unknownIdentifierMessageTag;
v___x_1159_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v_a_1154_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1164_, lean_object* v_declHint_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1164_, v_declHint_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v_env_1185_; uint8_t v___x_1186_; lean_object* v_env_1187_; lean_object* v___x_1188_; lean_object* v_toCold_1189_; lean_object* v_mctx_1190_; lean_object* v_lctx_1191_; lean_object* v_options_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1184_ = lean_st_ref_get(v___y_1182_);
v_env_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc_ref(v_env_1185_);
lean_dec(v___x_1184_);
v___x_1186_ = 0;
v_env_1187_ = l_Lean_Environment_setRecordingDeps(v_env_1185_, v___x_1186_);
v___x_1188_ = lean_st_ref_get(v___y_1180_);
v_toCold_1189_ = lean_ctor_get(v___y_1181_, 0);
v_mctx_1190_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_mctx_1190_);
lean_dec(v___x_1188_);
v_lctx_1191_ = lean_ctor_get(v___y_1179_, 2);
v_options_1192_ = lean_ctor_get(v_toCold_1189_, 2);
lean_inc_ref(v_options_1192_);
lean_inc_ref(v_lctx_1191_);
v___x_1193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1193_, 0, v_env_1187_);
lean_ctor_set(v___x_1193_, 1, v_mctx_1190_);
lean_ctor_set(v___x_1193_, 2, v_lctx_1191_);
lean_ctor_set(v___x_1193_, 3, v_options_1192_);
v___x_1194_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_msgData_1178_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_ref_1209_; lean_object* v___x_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_ref_1209_ = lean_ctor_get(v___y_1206_, 2);
v___x_1210_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_inc(v_ref_1209_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_ref_1209_);
lean_ctor_set(v___x_1215_, 1, v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1227_, lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_toCold_1240_; lean_object* v_currRecDepth_1241_; lean_object* v_ref_1242_; uint16_t v_optionFlags_1243_; uint8_t v_suppressElabErrors_1244_; uint8_t v_isRecordingDeps_1245_; lean_object* v_ref_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_toCold_1240_ = lean_ctor_get(v___y_1237_, 0);
v_currRecDepth_1241_ = lean_ctor_get(v___y_1237_, 1);
v_ref_1242_ = lean_ctor_get(v___y_1237_, 2);
v_optionFlags_1243_ = lean_ctor_get_uint16(v___y_1237_, sizeof(void*)*3);
v_suppressElabErrors_1244_ = lean_ctor_get_uint8(v___y_1237_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1245_ = lean_ctor_get_uint8(v___y_1237_, sizeof(void*)*3 + 3);
v_ref_1246_ = l_Lean_replaceRef(v_ref_1227_, v_ref_1242_);
lean_inc(v_currRecDepth_1241_);
lean_inc_ref(v_toCold_1240_);
v___x_1247_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1247_, 0, v_toCold_1240_);
lean_ctor_set(v___x_1247_, 1, v_currRecDepth_1241_);
lean_ctor_set(v___x_1247_, 2, v_ref_1246_);
lean_ctor_set_uint16(v___x_1247_, sizeof(void*)*3, v_optionFlags_1243_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*3 + 2, v_suppressElabErrors_1244_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*3 + 3, v_isRecordingDeps_1245_);
v___x_1248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1228_, v___y_1235_, v___y_1236_, v___x_1247_, v___y_1238_);
lean_dec_ref_known(v___x_1247_, 3);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1249_, v_msg_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v_ref_1249_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1263_, lean_object* v_msg_1264_, lean_object* v_declHint_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; 
v___x_1277_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1264_, v_declHint_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1263_, v_a_1278_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1280_, lean_object* v_msg_1281_, lean_object* v_declHint_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1280_, v_msg_1281_, v_declHint_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v_ref_1280_);
return v_res_1294_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1301_, lean_object* v_constName_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1314_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1315_ = 0;
lean_inc(v_constName_1302_);
v___x_1316_ = l_Lean_MessageData_ofConstName(v_constName_1302_, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1314_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1301_, v___x_1319_, v_constName_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1321_, lean_object* v_constName_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1321_, v_constName_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec(v_ref_1321_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_ref_1347_; lean_object* v___x_1348_; 
v_ref_1347_ = lean_ctor_get(v___y_1344_, 2);
v___x_1348_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1347_, v_constName_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_env_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_st_ref_get(v___y_1372_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = 0;
lean_inc(v_constName_1362_);
v___x_1377_ = l_Lean_Environment_find_x3f(v_env_1375_, v_constName_1362_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1378_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_constName_1362_);
v_val_1379_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1377_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_val_1379_);
lean_dec(v___x_1377_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 0);
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_val_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
return v_res_1399_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1400_; double v___x_1401_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_float_of_nat(v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1459_; 
v_ref_1412_ = lean_ctor_get(v___y_1409_, 2);
v___x_1413_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1459_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1459_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v_traceState_1419_; lean_object* v_env_1420_; lean_object* v_nextMacroScope_1421_; lean_object* v_ngen_1422_; lean_object* v_auxDeclNGen_1423_; lean_object* v_cache_1424_; lean_object* v_recordedDeps_1425_; lean_object* v_messages_1426_; lean_object* v_infoState_1427_; lean_object* v_snapshotTasks_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1458_; 
v___x_1418_ = lean_st_ref_take(v___y_1410_);
v_traceState_1419_ = lean_ctor_get(v___x_1418_, 4);
v_env_1420_ = lean_ctor_get(v___x_1418_, 0);
v_nextMacroScope_1421_ = lean_ctor_get(v___x_1418_, 1);
v_ngen_1422_ = lean_ctor_get(v___x_1418_, 2);
v_auxDeclNGen_1423_ = lean_ctor_get(v___x_1418_, 3);
v_cache_1424_ = lean_ctor_get(v___x_1418_, 5);
v_recordedDeps_1425_ = lean_ctor_get(v___x_1418_, 6);
v_messages_1426_ = lean_ctor_get(v___x_1418_, 7);
v_infoState_1427_ = lean_ctor_get(v___x_1418_, 8);
v_snapshotTasks_1428_ = lean_ctor_get(v___x_1418_, 9);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1430_ = v___x_1418_;
v_isShared_1431_ = v_isSharedCheck_1458_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snapshotTasks_1428_);
lean_inc(v_infoState_1427_);
lean_inc(v_messages_1426_);
lean_inc(v_recordedDeps_1425_);
lean_inc(v_cache_1424_);
lean_inc(v_traceState_1419_);
lean_inc(v_auxDeclNGen_1423_);
lean_inc(v_ngen_1422_);
lean_inc(v_nextMacroScope_1421_);
lean_inc(v_env_1420_);
lean_dec(v___x_1418_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1458_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint64_t v_tid_1432_; lean_object* v_traces_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1457_; 
v_tid_1432_ = lean_ctor_get_uint64(v_traceState_1419_, sizeof(void*)*1);
v_traces_1433_ = lean_ctor_get(v_traceState_1419_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_traceState_1419_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1435_ = v_traceState_1419_;
v_isShared_1436_ = v_isSharedCheck_1457_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_traces_1433_);
lean_dec(v_traceState_1419_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1457_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; double v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1440_ = 0;
v___x_1441_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1442_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1442_, 0, v_cls_1405_);
lean_ctor_set(v___x_1442_, 1, v___x_1438_);
lean_ctor_set(v___x_1442_, 2, v___x_1441_);
lean_ctor_set_float(v___x_1442_, sizeof(void*)*3, v___x_1439_);
lean_ctor_set_float(v___x_1442_, sizeof(void*)*3 + 8, v___x_1439_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*3 + 16, v___x_1440_);
v___x_1443_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1444_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v_a_1414_);
lean_ctor_set(v___x_1444_, 2, v___x_1443_);
lean_inc(v_ref_1412_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_ref_1412_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_Lean_PersistentArray_push___redArg(v_traces_1433_, v___x_1445_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1446_);
v___x_1448_ = v___x_1435_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1446_);
lean_ctor_set_uint64(v_reuseFailAlloc_1456_, sizeof(void*)*1, v_tid_1432_);
v___x_1448_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1448_);
v___x_1450_ = v___x_1430_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_env_1420_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_nextMacroScope_1421_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_ngen_1422_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_auxDeclNGen_1423_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1455_, 5, v_cache_1424_);
lean_ctor_set(v_reuseFailAlloc_1455_, 6, v_recordedDeps_1425_);
lean_ctor_set(v_reuseFailAlloc_1455_, 7, v_messages_1426_);
lean_ctor_set(v_reuseFailAlloc_1455_, 8, v_infoState_1427_);
lean_ctor_set(v_reuseFailAlloc_1455_, 9, v_snapshotTasks_1428_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_st_ref_put(v___y_1410_, v___x_1450_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1437_);
v___x_1453_ = v___x_1416_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1437_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1460_, lean_object* v_msg_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1460_, v_msg_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1470_ = l_Lean_stringToMessageData(v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1486_ = l_Lean_Name_append(v___x_1485_, v___x_1484_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
uint8_t v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; uint8_t v___y_1637_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___x_1765_; 
lean_inc_ref(v_e_1499_);
v___x_1765_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1499_, v_a_1507_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1794_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1794_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1794_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = l_Lean_Expr_cleanupAnnotations(v_a_1766_);
v___x_1771_ = l_Lean_Expr_isApp(v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec_ref(v___x_1770_);
lean_del_object(v___x_1768_);
v___y_1753_ = v_a_1500_;
v___y_1754_ = v_a_1501_;
v___y_1755_ = v_a_1502_;
v___y_1756_ = v_a_1503_;
v___y_1757_ = v_a_1504_;
v___y_1758_ = v_a_1505_;
v___y_1759_ = v_a_1506_;
v___y_1760_ = v_a_1507_;
v___y_1761_ = v_a_1508_;
v___y_1762_ = v_a_1509_;
goto v___jp_1752_;
}
else
{
lean_object* v_arg_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_arg_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc_ref(v_arg_1772_);
v___x_1773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1770_);
v___x_1774_ = l_Lean_Expr_isApp(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_arg_1772_);
lean_del_object(v___x_1768_);
v___y_1753_ = v_a_1500_;
v___y_1754_ = v_a_1501_;
v___y_1755_ = v_a_1502_;
v___y_1756_ = v_a_1503_;
v___y_1757_ = v_a_1504_;
v___y_1758_ = v_a_1505_;
v___y_1759_ = v_a_1506_;
v___y_1760_ = v_a_1507_;
v___y_1761_ = v_a_1508_;
v___y_1762_ = v_a_1509_;
goto v___jp_1752_;
}
else
{
lean_object* v_arg_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_arg_1775_ = lean_ctor_get(v___x_1773_, 1);
lean_inc_ref(v_arg_1775_);
v___x_1776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1773_);
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1778_ = l_Lean_Expr_isConstOf(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1780_ = l_Lean_Expr_isConstOf(v___x_1776_, v___x_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Lean_Expr_isApp(v___x_1776_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v___x_1776_);
lean_dec_ref(v_arg_1775_);
lean_dec_ref(v_arg_1772_);
lean_del_object(v___x_1768_);
v___y_1753_ = v_a_1500_;
v___y_1754_ = v_a_1501_;
v___y_1755_ = v_a_1502_;
v___y_1756_ = v_a_1503_;
v___y_1757_ = v_a_1504_;
v___y_1758_ = v_a_1505_;
v___y_1759_ = v_a_1506_;
v___y_1760_ = v_a_1507_;
v___y_1761_ = v_a_1508_;
v___y_1762_ = v_a_1509_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1776_);
v___x_1783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1784_ = l_Lean_Expr_isConstOf(v___x_1782_, v___x_1783_);
lean_dec_ref(v___x_1782_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v_arg_1775_);
lean_dec_ref(v_arg_1772_);
lean_del_object(v___x_1768_);
v___y_1753_ = v_a_1500_;
v___y_1754_ = v_a_1501_;
v___y_1755_ = v_a_1502_;
v___y_1756_ = v_a_1503_;
v___y_1757_ = v_a_1504_;
v___y_1758_ = v_a_1505_;
v___y_1759_ = v_a_1506_;
v___y_1760_ = v_a_1507_;
v___y_1761_ = v_a_1508_;
v___y_1762_ = v_a_1509_;
goto v___jp_1752_;
}
else
{
uint8_t v___x_1785_; 
lean_inc_ref(v_e_1499_);
v___x_1785_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1499_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_dec_ref(v_arg_1775_);
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_e_1499_);
v___x_1786_ = lean_unsigned_to_nat(2u);
v___x_1787_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*1, v___x_1785_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*1 + 1, v___x_1785_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1787_);
v___x_1789_ = v___x_1768_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
else
{
lean_object* v___x_1791_; 
lean_del_object(v___x_1768_);
v___x_1791_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1499_, v_arg_1775_, v_arg_1772_, v_a_1500_, v_a_1504_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1791_;
}
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec_ref(v___x_1776_);
lean_del_object(v___x_1768_);
v___x_1792_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1499_, v_arg_1775_, v_arg_1772_, v_a_1500_, v_a_1504_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1792_;
}
}
else
{
lean_object* v___x_1793_; 
lean_dec_ref(v___x_1776_);
lean_del_object(v___x_1768_);
v___x_1793_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1499_, v_arg_1775_, v_arg_1772_, v_a_1500_, v_a_1504_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_e_1499_);
v_a_1795_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1765_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1765_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
v___jp_1511_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
v___jp_1514_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
v___jp_1517_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
v___jp_1520_:
{
uint8_t v___x_1532_; 
v___x_1532_ = l_Lean_Expr_isFVar(v_e_1499_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec_ref(v_e_1499_);
v___x_1533_ = lean_box(1);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; 
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc_ref(v_e_1499_);
v___x_1535_ = lean_infer_type(v_e_1499_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = l_Lean_Meta_whnfD(v_a_1536_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc_n(v_a_1538_, 2);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1540_ = l_Lean_MessageData_ofExpr(v_e_1499_);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = l_Lean_indentExpr(v_a_1538_);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_Expr_getAppFn(v_a_1538_);
lean_dec(v_a_1538_);
if (lean_obj_tag(v___x_1546_) == 4)
{
lean_object* v_declName_1547_; lean_object* v___x_1548_; 
v_declName_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_declName_1547_);
lean_dec_ref_known(v___x_1546_, 2);
v___x_1548_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1547_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1581_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1581_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1581_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
if (lean_obj_tag(v_a_1549_) == 5)
{
lean_object* v_val_1553_; lean_object* v_ctors_1554_; uint8_t v_isRec_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_dec_ref_known(v___x_1545_, 2);
v_val_1553_ = lean_ctor_get(v_a_1549_, 0);
lean_inc_ref(v_val_1553_);
lean_dec_ref_known(v_a_1549_, 1);
v_ctors_1554_ = lean_ctor_get(v_val_1553_, 4);
lean_inc(v_ctors_1554_);
v_isRec_1555_ = lean_ctor_get_uint8(v_val_1553_, sizeof(void*)*6);
lean_dec_ref(v_val_1553_);
v___x_1556_ = l_List_lengthTR___redArg(v_ctors_1554_);
lean_dec(v_ctors_1554_);
v___x_1557_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*1, v_isRec_1555_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*1 + 1, v___y_1521_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1557_);
v___x_1559_ = v___x_1551_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
lean_object* v___x_1561_; 
lean_del_object(v___x_1551_);
lean_dec(v_a_1549_);
v___x_1561_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1526_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; uint8_t v_verbose_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_verbose_1563_ = lean_ctor_get_uint8(v_a_1562_, 0);
lean_dec(v_a_1562_);
if (v_verbose_1563_ == 0)
{
lean_dec_ref_known(v___x_1545_, 2);
goto v___jp_1514_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Sym_reportIssue(v___x_1545_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref_known(v___x_1564_, 1);
goto v___jp_1514_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref_known(v___x_1545_, 2);
v_a_1573_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1561_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1561_);
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
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref_known(v___x_1545_, 2);
v_a_1582_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1548_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1548_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v___x_1590_; 
lean_dec_ref(v___x_1546_);
v___x_1590_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1526_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; uint8_t v_verbose_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v_verbose_1592_ = lean_ctor_get_uint8(v_a_1591_, 0);
lean_dec(v_a_1591_);
if (v_verbose_1592_ == 0)
{
lean_dec_ref_known(v___x_1545_, 2);
goto v___jp_1517_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Meta_Sym_reportIssue(v___x_1545_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_dec_ref_known(v___x_1593_, 1);
goto v___jp_1517_;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
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
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref_known(v___x_1545_, 2);
v_a_1602_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1590_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1590_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v_e_1499_);
v_a_1610_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1537_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1537_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_e_1499_);
v_a_1618_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1535_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1535_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
v___jp_1626_:
{
if (v___y_1637_ == 0)
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1499_, v___y_1629_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; uint8_t v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_inc_ref(v_e_1499_);
v___x_1641_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1499_, v___y_1629_, v___y_1633_, v___y_1628_, v___y_1636_, v___y_1634_, v___y_1632_, v___y_1627_, v___y_1631_, v___y_1635_, v___y_1630_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1701_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1701_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1701_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_unbox(v_a_1642_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v_env_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_st_ref_get(v___y_1630_);
v_env_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc_ref(v_env_1648_);
lean_dec(v___x_1647_);
v___x_1649_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1648_, v_e_1499_);
if (lean_obj_tag(v___x_1649_) == 1)
{
lean_object* v_val_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1656_; 
lean_dec_ref(v_e_1499_);
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1650_);
lean_dec(v_val_1650_);
v___x_1652_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
v___x_1653_ = lean_unbox(v_a_1642_);
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*1, v___x_1653_);
v___x_1654_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*1 + 1, v___x_1654_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1652_);
v___x_1656_ = v___x_1644_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1652_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
else
{
lean_object* v___x_1658_; 
lean_dec(v___x_1649_);
lean_del_object(v___x_1644_);
v___x_1658_ = l_Lean_Expr_getAppFn(v_e_1499_);
if (lean_obj_tag(v___x_1658_) == 4)
{
lean_object* v_declName_1659_; lean_object* v___x_1660_; 
v_declName_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_declName_1659_);
lean_dec_ref_known(v___x_1658_, 2);
v___x_1660_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1659_, v___y_1627_, v___y_1631_, v___y_1635_, v___y_1630_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
if (lean_obj_tag(v_a_1661_) == 1)
{
lean_object* v_val_1662_; lean_object* v___x_1663_; 
v_val_1662_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v_a_1661_, 1);
lean_inc_ref(v_e_1499_);
v___x_1663_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1499_, v___y_1629_, v___y_1634_, v___y_1627_, v___y_1631_, v___y_1635_, v___y_1630_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1678_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1678_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1678_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_unbox(v_a_1664_);
lean_dec(v_a_1664_);
if (v___x_1668_ == 0)
{
uint8_t v___x_1669_; 
lean_del_object(v___x_1666_);
lean_dec(v_val_1662_);
v___x_1669_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
v___y_1521_ = v___x_1669_;
v___y_1522_ = v___y_1629_;
v___y_1523_ = v___y_1633_;
v___y_1524_ = v___y_1628_;
v___y_1525_ = v___y_1636_;
v___y_1526_ = v___y_1634_;
v___y_1527_ = v___y_1632_;
v___y_1528_ = v___y_1627_;
v___y_1529_ = v___y_1631_;
v___y_1530_ = v___y_1635_;
v___y_1531_ = v___y_1630_;
goto v___jp_1520_;
}
else
{
lean_object* v_ctors_1670_; uint8_t v_isRec_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1676_; 
lean_dec_ref(v_e_1499_);
v_ctors_1670_ = lean_ctor_get(v_val_1662_, 4);
lean_inc(v_ctors_1670_);
v_isRec_1671_ = lean_ctor_get_uint8(v_val_1662_, sizeof(void*)*6);
lean_dec(v_val_1662_);
v___x_1672_ = l_List_lengthTR___redArg(v_ctors_1670_);
lean_dec(v_ctors_1670_);
v___x_1673_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*1, v_isRec_1671_);
v___x_1674_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*1 + 1, v___x_1674_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1673_);
v___x_1676_ = v___x_1666_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1673_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_val_1662_);
lean_dec(v_a_1642_);
lean_dec_ref(v_e_1499_);
v_a_1679_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1663_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1663_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
uint8_t v___x_1687_; 
lean_dec(v_a_1661_);
v___x_1687_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
v___y_1521_ = v___x_1687_;
v___y_1522_ = v___y_1629_;
v___y_1523_ = v___y_1633_;
v___y_1524_ = v___y_1628_;
v___y_1525_ = v___y_1636_;
v___y_1526_ = v___y_1634_;
v___y_1527_ = v___y_1632_;
v___y_1528_ = v___y_1627_;
v___y_1529_ = v___y_1631_;
v___y_1530_ = v___y_1635_;
v___y_1531_ = v___y_1630_;
goto v___jp_1520_;
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_a_1642_);
lean_dec_ref(v_e_1499_);
v_a_1688_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1660_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1660_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
uint8_t v___x_1696_; 
lean_dec_ref(v___x_1658_);
v___x_1696_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
v___y_1521_ = v___x_1696_;
v___y_1522_ = v___y_1629_;
v___y_1523_ = v___y_1633_;
v___y_1524_ = v___y_1628_;
v___y_1525_ = v___y_1636_;
v___y_1526_ = v___y_1634_;
v___y_1527_ = v___y_1632_;
v___y_1528_ = v___y_1627_;
v___y_1529_ = v___y_1631_;
v___y_1530_ = v___y_1635_;
v___y_1531_ = v___y_1630_;
goto v___jp_1520_;
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_dec(v_a_1642_);
lean_dec_ref(v_e_1499_);
v___x_1697_ = lean_box(0);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1697_);
v___x_1699_ = v___x_1644_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_e_1499_);
v_a_1702_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1641_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1641_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_toCold_1710_; lean_object* v_options_1711_; uint8_t v_hasTrace_1712_; 
v_toCold_1710_ = lean_ctor_get(v___y_1635_, 0);
v_options_1711_ = lean_ctor_get(v_toCold_1710_, 2);
v_hasTrace_1712_ = lean_ctor_get_uint8(v_options_1711_, sizeof(void*)*1);
if (v_hasTrace_1712_ == 0)
{
lean_dec_ref(v_e_1499_);
goto v___jp_1511_;
}
else
{
lean_object* v_inheritedTraceOptions_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_inheritedTraceOptions_1713_ = lean_ctor_get(v_toCold_1710_, 11);
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1713_, v_options_1711_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_dec_ref(v_e_1499_);
goto v___jp_1511_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Meta_Grind_updateLastTag(v___y_1629_, v___y_1633_, v___y_1628_, v___y_1636_, v___y_1634_, v___y_1632_, v___y_1627_, v___y_1631_, v___y_1635_, v___y_1630_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref_known(v___x_1717_, 1);
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1719_ = l_Lean_MessageData_ofExpr(v_e_1499_);
v___x_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1714_, v___x_1720_, v___y_1627_, v___y_1631_, v___y_1635_, v___y_1630_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_dec_ref_known(v___x_1721_, 1);
goto v___jp_1511_;
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec_ref(v_e_1499_);
v_a_1730_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1717_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1717_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_e_1499_);
v_a_1738_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1638_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1638_);
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
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = l_Lean_Expr_getAppNumArgs(v_e_1499_);
v___x_1748_ = lean_nat_sub(v___x_1747_, v___x_1746_);
lean_dec(v___x_1747_);
v___x_1749_ = lean_nat_sub(v___x_1748_, v___x_1746_);
lean_dec(v___x_1748_);
v___x_1750_ = l_Lean_Expr_getRevArg_x21(v_e_1499_, v___x_1749_);
lean_dec_ref(v_e_1499_);
v___x_1751_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1750_, v___y_1629_, v___y_1634_, v___y_1627_, v___y_1631_, v___y_1635_, v___y_1630_);
return v___x_1751_;
}
}
v___jp_1752_:
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_Meta_Grind_isIte(v_e_1499_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_Meta_Grind_isDIte(v_e_1499_);
v___y_1627_ = v___y_1759_;
v___y_1628_ = v___y_1755_;
v___y_1629_ = v___y_1753_;
v___y_1630_ = v___y_1762_;
v___y_1631_ = v___y_1760_;
v___y_1632_ = v___y_1758_;
v___y_1633_ = v___y_1754_;
v___y_1634_ = v___y_1757_;
v___y_1635_ = v___y_1761_;
v___y_1636_ = v___y_1756_;
v___y_1637_ = v___x_1764_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v___y_1759_;
v___y_1628_ = v___y_1755_;
v___y_1629_ = v___y_1753_;
v___y_1630_ = v___y_1762_;
v___y_1631_ = v___y_1760_;
v___y_1632_ = v___y_1758_;
v___y_1633_ = v___y_1754_;
v___y_1634_ = v___y_1757_;
v___y_1635_ = v___y_1761_;
v___y_1636_ = v___y_1756_;
v___y_1637_ = v___x_1763_;
goto v___jp_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec(v_a_1804_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1816_, lean_object* v_msg_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1816_, v_msg_1817_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1830_, lean_object* v_msg_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1830_, v_msg_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec(v___y_1832_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1844_, lean_object* v_constName_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_constName_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1858_, v_constName_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1872_, lean_object* v_ref_1873_, lean_object* v_constName_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1873_, v_constName_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_ref_1888_, lean_object* v_constName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1887_, v_ref_1888_, v_constName_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v_ref_1888_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1902_, lean_object* v_ref_1903_, lean_object* v_msg_1904_, lean_object* v_declHint_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1903_, v_msg_1904_, v_declHint_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_ref_1919_, lean_object* v_msg_1920_, lean_object* v_declHint_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1918_, v_ref_1919_, v_msg_1920_, v_declHint_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec(v_ref_1919_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1934_, lean_object* v_declHint_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1934_, v_declHint_1935_, v___y_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1948_, lean_object* v_declHint_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1948_, v_declHint_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
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
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1962_, lean_object* v_ref_1963_, lean_object* v_msg_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1963_, v_msg_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1977_, lean_object* v_ref_1978_, lean_object* v_msg_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1977_, v_ref_1978_, v_msg_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec(v_ref_1978_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1992_, lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1993_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_msg_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2006_, v_msg_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
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
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2020_, lean_object* v_x_2021_){
_start:
{
if (lean_obj_tag(v_x_2021_) == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_box(0);
return v___x_2022_;
}
else
{
lean_object* v_key_2023_; lean_object* v_value_2024_; lean_object* v_tail_2025_; uint8_t v___y_2027_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v_fst_2032_; lean_object* v_snd_2033_; uint8_t v___x_2034_; 
v_key_2023_ = lean_ctor_get(v_x_2021_, 0);
v_value_2024_ = lean_ctor_get(v_x_2021_, 1);
v_tail_2025_ = lean_ctor_get(v_x_2021_, 2);
v_fst_2030_ = lean_ctor_get(v_key_2023_, 0);
v_snd_2031_ = lean_ctor_get(v_key_2023_, 1);
v_fst_2032_ = lean_ctor_get(v_a_2020_, 0);
v_snd_2033_ = lean_ctor_get(v_a_2020_, 1);
v___x_2034_ = lean_expr_eqv(v_fst_2030_, v_fst_2032_);
if (v___x_2034_ == 0)
{
v___y_2027_ = v___x_2034_;
goto v___jp_2026_;
}
else
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_expr_eqv(v_snd_2031_, v_snd_2033_);
v___y_2027_ = v___x_2035_;
goto v___jp_2026_;
}
v___jp_2026_:
{
if (v___y_2027_ == 0)
{
v_x_2021_ = v_tail_2025_;
goto _start;
}
else
{
lean_object* v___x_2029_; 
lean_inc(v_value_2024_);
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_value_2024_);
return v___x_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2036_, v_x_2037_);
lean_dec(v_x_2037_);
lean_dec_ref(v_a_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_buckets_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2044_; uint64_t v___x_2045_; uint64_t v___x_2046_; uint64_t v___x_2047_; uint64_t v___x_2048_; uint64_t v___x_2049_; uint64_t v_fold_2050_; uint64_t v___x_2051_; uint64_t v___x_2052_; uint64_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_buckets_2041_ = lean_ctor_get(v_m_2039_, 1);
v_fst_2042_ = lean_ctor_get(v_a_2040_, 0);
v_snd_2043_ = lean_ctor_get(v_a_2040_, 1);
v___x_2044_ = lean_array_get_size(v_buckets_2041_);
v___x_2045_ = l_Lean_Expr_hash(v_fst_2042_);
v___x_2046_ = l_Lean_Expr_hash(v_snd_2043_);
v___x_2047_ = lean_uint64_mix_hash(v___x_2045_, v___x_2046_);
v___x_2048_ = 32ULL;
v___x_2049_ = lean_uint64_shift_right(v___x_2047_, v___x_2048_);
v_fold_2050_ = lean_uint64_xor(v___x_2047_, v___x_2049_);
v___x_2051_ = 16ULL;
v___x_2052_ = lean_uint64_shift_right(v_fold_2050_, v___x_2051_);
v___x_2053_ = lean_uint64_xor(v_fold_2050_, v___x_2052_);
v___x_2054_ = lean_uint64_to_usize(v___x_2053_);
v___x_2055_ = lean_usize_of_nat(v___x_2044_);
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_sub(v___x_2055_, v___x_2056_);
v___x_2058_ = lean_usize_land(v___x_2054_, v___x_2057_);
v___x_2059_ = lean_array_uget_borrowed(v_buckets_2041_, v___x_2058_);
v___x_2060_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2040_, v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2061_, v_a_2062_);
lean_dec_ref(v_a_2062_);
lean_dec_ref(v_m_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2064_, uint8_t v___x_2065_, lean_object* v_fst_2066_, lean_object* v_snd_2067_, lean_object* v___x_2068_, lean_object* v_____r_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2081_ = lean_unsigned_to_nat(2u);
v___x_2082_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1, v_a_2064_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1 + 1, v___x_2065_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_fst_2066_);
lean_ctor_set(v___x_2084_, 1, v_snd_2067_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2068_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2083_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2089_ = _args[0];
lean_object* v___x_2090_ = _args[1];
lean_object* v_fst_2091_ = _args[2];
lean_object* v_snd_2092_ = _args[3];
lean_object* v___x_2093_ = _args[4];
lean_object* v_____r_2094_ = _args[5];
lean_object* v___y_2095_ = _args[6];
lean_object* v___y_2096_ = _args[7];
lean_object* v___y_2097_ = _args[8];
lean_object* v___y_2098_ = _args[9];
lean_object* v___y_2099_ = _args[10];
lean_object* v___y_2100_ = _args[11];
lean_object* v___y_2101_ = _args[12];
lean_object* v___y_2102_ = _args[13];
lean_object* v___y_2103_ = _args[14];
lean_object* v___y_2104_ = _args[15];
lean_object* v___y_2105_ = _args[16];
_start:
{
uint8_t v_a_33765__boxed_2106_; uint8_t v___x_33766__boxed_2107_; lean_object* v_res_2108_; 
v_a_33765__boxed_2106_ = lean_unbox(v_a_2089_);
v___x_33766__boxed_2107_ = lean_unbox(v___x_2090_);
v_res_2108_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_33765__boxed_2106_, v___x_33766__boxed_2107_, v_fst_2091_, v_snd_2092_, v___x_2093_, v_____r_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2109_, lean_object* v_snd_2110_, lean_object* v___x_2111_, lean_object* v___x_2112_, lean_object* v_____r_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2125_ = l_Lean_Expr_appFn_x21(v_fst_2109_);
v___x_2126_ = l_Lean_Expr_appFn_x21(v_snd_2110_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2111_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2112_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2132_, lean_object* v_snd_2133_, lean_object* v___x_2134_, lean_object* v___x_2135_, lean_object* v_____r_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2132_, v_snd_2133_, v___x_2134_, v___x_2135_, v_____r_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
return v_res_2148_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___f_2150_; 
v___x_2149_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2150_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2150_, 0, v___x_2149_);
return v___f_2150_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2156_ = l_Lean_Name_append(v___x_2155_, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2168_ = l_Lean_stringToMessageData(v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2171_ = l_Lean_stringToMessageData(v___x_2170_);
return v___x_2171_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2175_, lean_object* v___y_2176_, lean_object* v_eq_2177_, lean_object* v_a_2178_, lean_object* v_b_2179_, lean_object* v_a_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___y_2193_; lean_object* v_snd_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2336_; 
v_snd_2213_ = lean_ctor_get(v_a_2180_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_a_2180_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v_a_2180_, 0);
lean_dec(v_unused_2337_);
v___x_2215_ = v_a_2180_;
v_isShared_2216_ = v_isSharedCheck_2336_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_snd_2213_);
lean_dec(v_a_2180_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2336_;
goto v_resetjp_2214_;
}
v___jp_2192_:
{
if (lean_obj_tag(v___y_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2204_; 
v_a_2194_ = lean_ctor_get(v___y_2193_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___y_2193_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2196_ = v___y_2193_;
v_isShared_2197_ = v_isSharedCheck_2204_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___y_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2204_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
if (lean_obj_tag(v_a_2194_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; 
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v_a_2198_ = lean_ctor_get(v_a_2194_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v_a_2194_, 1);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_a_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
else
{
lean_object* v_a_2202_; 
lean_del_object(v___x_2196_);
v_a_2202_ = lean_ctor_get(v_a_2194_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v_a_2194_, 1);
v_a_2180_ = v_a_2202_;
goto _start;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v_a_2205_ = lean_ctor_get(v___y_2193_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___y_2193_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___y_2193_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___y_2193_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
v_resetjp_2214_:
{
lean_object* v_snd_2217_; lean_object* v_fst_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2335_; 
v_snd_2217_ = lean_ctor_get(v_snd_2213_, 1);
v_fst_2218_ = lean_ctor_get(v_snd_2213_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_snd_2213_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2220_ = v_snd_2213_;
v_isShared_2221_ = v_isSharedCheck_2335_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_snd_2217_);
lean_inc(v_fst_2218_);
lean_dec(v_snd_2213_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2335_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2334_; 
v_fst_2222_ = lean_ctor_get(v_snd_2217_, 0);
v_snd_2223_ = lean_ctor_get(v_snd_2217_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_snd_2217_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2225_ = v_snd_2217_;
v_isShared_2226_ = v_isSharedCheck_2334_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_snd_2223_);
lean_inc(v_fst_2222_);
lean_dec(v_snd_2217_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2334_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
uint8_t v___y_2228_; uint8_t v___x_2242_; 
v___x_2242_ = l_Lean_Expr_isApp(v_fst_2222_);
if (v___x_2242_ == 0)
{
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v___y_2228_ = v_a_2175_;
goto v___jp_2227_;
}
else
{
uint8_t v___x_2243_; 
v___x_2243_ = l_Lean_Expr_isApp(v_snd_2223_);
if (v___x_2243_ == 0)
{
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v___y_2228_ = v___x_2243_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___f_2250_; uint8_t v___x_2251_; 
lean_del_object(v___x_2225_);
lean_del_object(v___x_2220_);
lean_del_object(v___x_2215_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_sub(v_fst_2218_, v___x_2245_);
lean_dec(v_fst_2218_);
v___f_2250_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2176_);
lean_inc(v___x_2246_);
v___x_2251_ = l_List_elem___redArg(v___f_2250_, v___x_2246_, v___y_2176_);
if (v___x_2251_ == 0)
{
if (v___x_2243_ == 0)
{
goto v___jp_2247_;
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = l_Lean_Expr_appArg_x21(v_fst_2222_);
v___x_2253_ = l_Lean_Expr_appArg_x21(v_snd_2223_);
v___x_2254_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2252_, v___x_2253_, v___y_2181_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; uint8_t v___x_2256_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2256_ = lean_unbox(v_a_2255_);
if (v___x_2256_ == 0)
{
lean_object* v_toCold_2257_; lean_object* v_options_2258_; lean_object* v_inheritedTraceOptions_2259_; uint8_t v_hasTrace_2260_; 
v_toCold_2257_ = lean_ctor_get(v___y_2189_, 0);
v_options_2258_ = lean_ctor_get(v_toCold_2257_, 2);
v_inheritedTraceOptions_2259_ = lean_ctor_get(v_toCold_2257_, 11);
v_hasTrace_2260_ = lean_ctor_get_uint8(v_options_2258_, sizeof(void*)*1);
if (v_hasTrace_2260_ == 0)
{
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
goto v___jp_2261_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2265_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2266_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2267_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2259_, v_options_2258_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
goto v___jp_2261_;
}
else
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_Grind_updateLastTag(v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref_known(v___x_2268_, 1);
v___x_2269_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2177_, v___y_2181_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2178_);
v___x_2272_ = l_Lean_MessageData_ofExpr(v_a_2178_);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
lean_inc_ref(v_b_2179_);
v___x_2276_ = l_Lean_MessageData_ofExpr(v_b_2179_);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
lean_inc_ref(v_eq_2177_);
v___x_2280_ = l_Lean_MessageData_ofExpr(v_eq_2177_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_MessageData_ofExpr(v___x_2252_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_MessageData_ofExpr(v___x_2253_);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Nat_reprFast(v_a_2270_);
v___x_2293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = l_Lean_MessageData_ofFormat(v___x_2293_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2291_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2265_, v___x_2295_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
v___x_2299_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2298_, v___x_2243_, v_fst_2222_, v_snd_2223_, v___x_2246_, v_a_2297_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
v___y_2193_ = v___x_2299_;
goto v___jp_2192_;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec(v_a_2255_);
lean_dec(v___x_2246_);
lean_dec(v_snd_2223_);
lean_dec(v_fst_2222_);
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v_a_2300_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2296_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2296_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2255_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
lean_dec(v___x_2246_);
lean_dec(v_snd_2223_);
lean_dec(v_fst_2222_);
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v_a_2308_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2269_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2269_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_a_2255_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
lean_dec(v___x_2246_);
lean_dec(v_snd_2223_);
lean_dec(v_fst_2222_);
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v_a_2316_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2268_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2268_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
v___jp_2261_:
{
lean_object* v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
v___x_2264_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2263_, v___x_2243_, v_fst_2222_, v_snd_2223_, v___x_2246_, v___x_2262_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
v___y_2193_ = v___x_2264_;
goto v___jp_2192_;
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_dec(v_a_2255_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
v___x_2324_ = lean_box(0);
v___x_2325_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2222_, v_snd_2223_, v___x_2246_, v___x_2244_, v___x_2324_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v_snd_2223_);
lean_dec(v_fst_2222_);
v___y_2193_ = v___x_2325_;
goto v___jp_2192_;
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
lean_dec(v___x_2246_);
lean_dec(v_snd_2223_);
lean_dec(v_fst_2222_);
lean_dec_ref(v_b_2179_);
lean_dec_ref(v_a_2178_);
lean_dec_ref(v_eq_2177_);
lean_dec(v___y_2176_);
v_a_2326_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2254_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2254_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
goto v___jp_2247_;
}
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2222_, v_snd_2223_, v___x_2246_, v___x_2244_, v___x_2248_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v_snd_2223_);
lean_dec(v_fst_2222_);
v___y_2193_ = v___x_2249_;
goto v___jp_2192_;
}
}
}
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2229_ = lean_unsigned_to_nat(2u);
v___x_2230_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*1, v___y_2228_);
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*1 + 1, v___y_2228_);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
if (v_isShared_2226_ == 0)
{
v___x_2233_ = v___x_2225_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_fst_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_snd_2223_);
v___x_2233_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2233_);
v___x_2235_ = v___x_2220_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_fst_2218_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2235_);
lean_ctor_set(v___x_2215_, 0, v___x_2231_);
v___x_2237_ = v___x_2215_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
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
lean_object* v_a_2338_ = _args[0];
lean_object* v___y_2339_ = _args[1];
lean_object* v_eq_2340_ = _args[2];
lean_object* v_a_2341_ = _args[3];
lean_object* v_b_2342_ = _args[4];
lean_object* v_a_2343_ = _args[5];
lean_object* v___y_2344_ = _args[6];
lean_object* v___y_2345_ = _args[7];
lean_object* v___y_2346_ = _args[8];
lean_object* v___y_2347_ = _args[9];
lean_object* v___y_2348_ = _args[10];
lean_object* v___y_2349_ = _args[11];
lean_object* v___y_2350_ = _args[12];
lean_object* v___y_2351_ = _args[13];
lean_object* v___y_2352_ = _args[14];
lean_object* v___y_2353_ = _args[15];
lean_object* v___y_2354_ = _args[16];
_start:
{
uint8_t v_a_33939__boxed_2355_; lean_object* v_res_2356_; 
v_a_33939__boxed_2355_ = lean_unbox(v_a_2338_);
v_res_2356_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_33939__boxed_2355_, v___y_2339_, v_eq_2340_, v_a_2341_, v_b_2342_, v_a_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2357_, lean_object* v_b_2358_, lean_object* v_eq_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2404_; lean_object* v___x_2440_; 
lean_inc_ref(v_eq_2359_);
v___x_2440_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2359_, v_a_2360_, v_a_2364_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; uint8_t v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v___x_2442_ = lean_unbox(v_a_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref_known(v___x_2440_, 1);
lean_inc_ref(v_eq_2359_);
v___x_2443_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2359_, v_a_2360_, v_a_2364_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
v___y_2404_ = v___x_2443_;
goto v___jp_2403_;
}
else
{
v___y_2404_ = v___x_2440_;
goto v___jp_2403_;
}
}
else
{
v___y_2404_ = v___x_2440_;
goto v___jp_2403_;
}
v___jp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2374_ = l_Lean_Expr_getAppNumArgs(v_a_2357_);
v___x_2375_ = lean_box(0);
lean_inc_ref(v_b_2358_);
lean_inc_ref(v_a_2357_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_a_2357_);
lean_ctor_set(v___x_2376_, 1, v_b_2358_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2374_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2375_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2372_, v___y_2373_, v_eq_2359_, v_a_2357_, v_b_2358_, v___x_2378_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2394_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_fst_2384_; 
v_fst_2384_ = lean_ctor_get(v_a_2380_, 0);
lean_inc(v_fst_2384_);
lean_dec(v_a_2380_);
if (lean_obj_tag(v_fst_2384_) == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2385_ = lean_unsigned_to_nat(2u);
v___x_2386_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1, v___y_2372_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1 + 1, v___y_2372_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2386_);
v___x_2388_ = v___x_2382_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2392_; 
v_val_2390_ = lean_ctor_get(v_fst_2384_, 0);
lean_inc(v_val_2390_);
lean_dec_ref_known(v_fst_2384_, 1);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v_val_2390_);
v___x_2392_ = v___x_2382_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_val_2390_);
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
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2379_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2379_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
v___jp_2403_:
{
if (lean_obj_tag(v___y_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2431_; 
v_a_2405_ = lean_ctor_get(v___y_2404_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___y_2404_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2407_ = v___y_2404_;
v_isShared_2408_ = v_isSharedCheck_2431_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___y_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2431_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_unbox(v_a_2405_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v_toGoalState_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2425_; 
lean_del_object(v___x_2407_);
v___x_2410_ = lean_st_ref_get(v_a_2360_);
v_toGoalState_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v___x_2410_, 1);
lean_dec(v_unused_2426_);
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2425_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_toGoalState_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2425_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_split_2415_; lean_object* v_argPosMap_2416_; lean_object* v___x_2418_; 
v_split_2415_ = lean_ctor_get(v_toGoalState_2411_, 14);
lean_inc_ref(v_split_2415_);
lean_dec_ref(v_toGoalState_2411_);
v_argPosMap_2416_ = lean_ctor_get(v_split_2415_, 6);
lean_inc_ref(v_argPosMap_2416_);
lean_dec_ref(v_split_2415_);
lean_inc_ref(v_b_2358_);
lean_inc_ref(v_a_2357_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v_b_2358_);
lean_ctor_set(v___x_2413_, 0, v_a_2357_);
v___x_2418_ = v___x_2413_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2357_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_b_2358_);
v___x_2418_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2416_, v___x_2418_);
lean_dec_ref(v___x_2418_);
lean_dec_ref(v_argPosMap_2416_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_unbox(v_a_2405_);
lean_dec(v_a_2405_);
v___y_2372_ = v___x_2421_;
v___y_2373_ = v___x_2420_;
goto v___jp_2371_;
}
else
{
lean_object* v_val_2422_; uint8_t v___x_2423_; 
v_val_2422_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_val_2422_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2423_ = lean_unbox(v_a_2405_);
lean_dec(v_a_2405_);
v___y_2372_ = v___x_2423_;
v___y_2373_ = v_val_2422_;
goto v___jp_2371_;
}
}
}
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
lean_dec(v_a_2405_);
lean_dec_ref(v_eq_2359_);
lean_dec_ref(v_b_2358_);
lean_dec_ref(v_a_2357_);
v___x_2427_ = lean_box(0);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2427_);
v___x_2429_ = v___x_2407_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v_eq_2359_);
lean_dec_ref(v_b_2358_);
lean_dec_ref(v_a_2357_);
v_a_2432_ = lean_ctor_get(v___y_2404_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___y_2404_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___y_2404_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___y_2404_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2444_, lean_object* v_b_2445_, lean_object* v_eq_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2444_, v_b_2445_, v_eq_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec(v_a_2447_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2459_, lean_object* v___y_2460_, lean_object* v_eq_2461_, lean_object* v_a_2462_, lean_object* v_b_2463_, lean_object* v_inst_2464_, lean_object* v_a_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2459_, v___y_2460_, v_eq_2461_, v_a_2462_, v_b_2463_, v_a_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2478_ = _args[0];
lean_object* v___y_2479_ = _args[1];
lean_object* v_eq_2480_ = _args[2];
lean_object* v_a_2481_ = _args[3];
lean_object* v_b_2482_ = _args[4];
lean_object* v_inst_2483_ = _args[5];
lean_object* v_a_2484_ = _args[6];
lean_object* v___y_2485_ = _args[7];
lean_object* v___y_2486_ = _args[8];
lean_object* v___y_2487_ = _args[9];
lean_object* v___y_2488_ = _args[10];
lean_object* v___y_2489_ = _args[11];
lean_object* v___y_2490_ = _args[12];
lean_object* v___y_2491_ = _args[13];
lean_object* v___y_2492_ = _args[14];
lean_object* v___y_2493_ = _args[15];
lean_object* v___y_2494_ = _args[16];
lean_object* v___y_2495_ = _args[17];
_start:
{
uint8_t v_a_34421__boxed_2496_; lean_object* v_res_2497_; 
v_a_34421__boxed_2496_ = lean_unbox(v_a_2478_);
v_res_2497_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34421__boxed_2496_, v___y_2479_, v_eq_2480_, v_a_2481_, v_b_2482_, v_inst_2483_, v_a_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2498_, lean_object* v_m_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2499_, v_a_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2502_, lean_object* v_m_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2502_, v_m_2503_, v_a_2504_);
lean_dec_ref(v_a_2504_);
lean_dec_ref(v_m_2503_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2506_, lean_object* v_a_2507_, lean_object* v_x_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2507_, v_x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2510_, lean_object* v_a_2511_, lean_object* v_x_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2510_, v_a_2511_, v_x_2512_);
lean_dec(v_x_2512_);
lean_dec_ref(v_a_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
uint8_t v___y_2523_; uint8_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___x_2548_; 
lean_inc_ref(v_imp_2514_);
v___x_2548_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = lean_unbox(v_a_2549_);
lean_dec(v_a_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2565_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2565_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2565_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_unbox(v_a_2552_);
lean_dec(v_a_2552_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_box(1);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2557_);
v___x_2559_ = v___x_2554_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = lean_box(0);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2561_);
v___x_2563_ = v___x_2554_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_a_2566_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2551_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2551_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
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
lean_object* v_binderType_2574_; lean_object* v_body_2575_; lean_object* v___y_2577_; lean_object* v___x_2605_; 
v_binderType_2574_ = lean_ctor_get(v_imp_2514_, 1);
lean_inc_ref_n(v_binderType_2574_, 2);
v_body_2575_ = lean_ctor_get(v_imp_2514_, 2);
lean_inc_ref(v_body_2575_);
lean_dec_ref(v_imp_2514_);
v___x_2605_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2574_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; uint8_t v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v___x_2607_ = lean_unbox(v_a_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_dec_ref_known(v___x_2605_, 1);
v___x_2608_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2574_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
v___y_2577_ = v___x_2608_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v_binderType_2574_);
v___y_2577_ = v___x_2605_;
goto v___jp_2576_;
}
}
else
{
lean_dec_ref(v_binderType_2574_);
v___y_2577_ = v___x_2605_;
goto v___jp_2576_;
}
v___jp_2576_:
{
if (lean_obj_tag(v___y_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2596_; 
v_a_2578_ = lean_ctor_get(v___y_2577_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___y_2577_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2580_ = v___y_2577_;
v_isShared_2581_ = v_isSharedCheck_2596_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___y_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2596_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_unbox(v_a_2578_);
if (v___x_2582_ == 0)
{
uint8_t v___x_2583_; 
lean_del_object(v___x_2580_);
v___x_2583_ = l_Lean_Expr_hasLooseBVars(v_body_2575_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
lean_inc_ref(v_body_2575_);
v___x_2584_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2575_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; uint8_t v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v___x_2586_ = lean_unbox(v_a_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2587_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2575_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
v___x_2588_ = lean_unbox(v_a_2578_);
lean_dec(v_a_2578_);
v___y_2528_ = v___x_2588_;
v___y_2529_ = v___x_2587_;
goto v___jp_2527_;
}
else
{
uint8_t v___x_2589_; 
lean_dec_ref(v_body_2575_);
v___x_2589_ = lean_unbox(v_a_2578_);
lean_dec(v_a_2578_);
v___y_2528_ = v___x_2589_;
v___y_2529_ = v___x_2584_;
goto v___jp_2527_;
}
}
else
{
uint8_t v___x_2590_; 
lean_dec_ref(v_body_2575_);
v___x_2590_ = lean_unbox(v_a_2578_);
lean_dec(v_a_2578_);
v___y_2528_ = v___x_2590_;
v___y_2529_ = v___x_2584_;
goto v___jp_2527_;
}
}
else
{
uint8_t v___x_2591_; 
lean_dec_ref(v_body_2575_);
v___x_2591_ = lean_unbox(v_a_2578_);
lean_dec(v_a_2578_);
v___y_2523_ = v___x_2591_;
goto v___jp_2522_;
}
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_dec(v_a_2578_);
lean_dec_ref(v_body_2575_);
v___x_2592_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2592_);
v___x_2594_ = v___x_2580_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v_body_2575_);
v_a_2597_ = lean_ctor_get(v___y_2577_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___y_2577_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___y_2577_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___y_2577_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v_imp_2514_);
v_a_2609_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2548_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2548_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
v___jp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = lean_unsigned_to_nat(2u);
v___x_2525_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*1, v___y_2523_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*1 + 1, v___y_2523_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
v___jp_2527_:
{
if (lean_obj_tag(v___y_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2539_; 
v_a_2530_ = lean_ctor_get(v___y_2529_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___y_2529_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2532_ = v___y_2529_;
v_isShared_2533_ = v_isSharedCheck_2539_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___y_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2539_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_unbox(v_a_2530_);
lean_dec(v_a_2530_);
if (v___x_2534_ == 0)
{
lean_del_object(v___x_2532_);
v___y_2523_ = v___y_2528_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_box(0);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2535_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___y_2529_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___y_2529_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___y_2529_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___y_2529_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2626_, lean_object* v_h_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2626_, v_a_2628_, v_a_2632_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2640_, lean_object* v_h_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2640_, v_h_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec(v_a_2642_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
switch(lean_obj_tag(v_s_2654_))
{
case 0:
{
lean_object* v_e_2666_; lean_object* v___x_2667_; 
v_e_2666_ = lean_ctor_get(v_s_2654_, 0);
lean_inc_ref(v_e_2666_);
lean_dec_ref_known(v_s_2654_, 2);
v___x_2667_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2666_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2667_;
}
case 1:
{
lean_object* v_e_2668_; lean_object* v___x_2669_; 
v_e_2668_ = lean_ctor_get(v_s_2654_, 0);
lean_inc_ref(v_e_2668_);
lean_dec_ref_known(v_s_2654_, 2);
v___x_2669_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2668_, v_a_2655_, v_a_2659_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2669_;
}
default: 
{
lean_object* v_a_2670_; lean_object* v_b_2671_; lean_object* v_eq_2672_; lean_object* v___x_2673_; 
v_a_2670_ = lean_ctor_get(v_s_2654_, 0);
lean_inc_ref(v_a_2670_);
v_b_2671_ = lean_ctor_get(v_s_2654_, 1);
lean_inc_ref(v_b_2671_);
v_eq_2672_ = lean_ctor_get(v_s_2654_, 3);
lean_inc_ref(v_eq_2672_);
lean_dec_ref_known(v_s_2654_, 5);
v___x_2673_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2670_, v_b_2671_, v_eq_2672_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec(v_a_2675_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_obj_tag_nat(v_x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2689_);
lean_dec(v_x_2689_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2691_, lean_object* v_k_2692_){
_start:
{
if (lean_obj_tag(v_t_2691_) == 0)
{
return v_k_2692_;
}
else
{
lean_object* v_c_2693_; lean_object* v_numCases_2694_; uint8_t v_isRec_2695_; uint8_t v_tryPostpone_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_c_2693_ = lean_ctor_get(v_t_2691_, 0);
lean_inc_ref(v_c_2693_);
v_numCases_2694_ = lean_ctor_get(v_t_2691_, 1);
lean_inc(v_numCases_2694_);
v_isRec_2695_ = lean_ctor_get_uint8(v_t_2691_, sizeof(void*)*2);
v_tryPostpone_2696_ = lean_ctor_get_uint8(v_t_2691_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2691_, 2);
v___x_2697_ = lean_box(v_isRec_2695_);
v___x_2698_ = lean_box(v_tryPostpone_2696_);
v___x_2699_ = lean_apply_4(v_k_2692_, v_c_2693_, v_numCases_2694_, v___x_2697_, v___x_2698_);
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2700_, lean_object* v_ctorIdx_2701_, lean_object* v_t_2702_, lean_object* v_h_2703_, lean_object* v_k_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2702_, v_k_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2706_, lean_object* v_ctorIdx_2707_, lean_object* v_t_2708_, lean_object* v_h_2709_, lean_object* v_k_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2706_, v_ctorIdx_2707_, v_t_2708_, v_h_2709_, v_k_2710_);
lean_dec(v_ctorIdx_2707_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2712_, lean_object* v_none_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2712_, v_none_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2715_, lean_object* v_t_2716_, lean_object* v_h_2717_, lean_object* v_none_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2716_, v_none_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2720_, lean_object* v_some_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2720_, v_some_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2723_, lean_object* v_t_2724_, lean_object* v_h_2725_, lean_object* v_some_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2724_, v_some_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2728_, lean_object* v_as_2729_, size_t v_i_2730_, size_t v_stop_2731_){
_start:
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_usize_dec_eq(v_i_2730_, v_stop_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_array_uget_borrowed(v_as_2729_, v_i_2730_);
v___x_2734_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2733_, v_a_2728_);
if (v___x_2734_ == 0)
{
size_t v___x_2735_; size_t v___x_2736_; 
v___x_2735_ = ((size_t)1ULL);
v___x_2736_ = lean_usize_add(v_i_2730_, v___x_2735_);
v_i_2730_ = v___x_2736_;
goto _start;
}
else
{
return v___x_2734_;
}
}
else
{
uint8_t v___x_2738_; 
v___x_2738_ = 0;
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2739_, lean_object* v_as_2740_, lean_object* v_i_2741_, lean_object* v_stop_2742_){
_start:
{
uint64_t v_a_2507__boxed_2743_; size_t v_i_boxed_2744_; size_t v_stop_boxed_2745_; uint8_t v_res_2746_; lean_object* v_r_2747_; 
v_a_2507__boxed_2743_ = lean_unbox_uint64(v_a_2739_);
lean_dec_ref(v_a_2739_);
v_i_boxed_2744_ = lean_unbox_usize(v_i_2741_);
lean_dec(v_i_2741_);
v_stop_boxed_2745_ = lean_unbox_usize(v_stop_2742_);
lean_dec(v_stop_2742_);
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2743_, v_as_2740_, v_i_boxed_2744_, v_stop_boxed_2745_);
lean_dec_ref(v_as_2740_);
v_r_2747_ = lean_box(v_res_2746_);
return v_r_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2750_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2803_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2803_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2803_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
if (lean_obj_tag(v_a_2760_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; 
lean_del_object(v___x_2762_);
v_val_2764_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_a_2760_, 1);
v___x_2765_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2789_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2789_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2789_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = lean_array_get_size(v_val_2764_);
v___x_2772_ = lean_nat_dec_lt(v___x_2770_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec(v_a_2766_);
lean_dec(v_val_2764_);
v___x_2773_ = lean_box(v___x_2772_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2773_);
v___x_2775_ = v___x_2768_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
if (v___x_2772_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec(v_a_2766_);
lean_dec(v_val_2764_);
v___x_2777_ = lean_box(v___x_2772_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2777_);
v___x_2779_ = v___x_2768_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
size_t v___x_2781_; size_t v___x_2782_; uint64_t v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2781_ = ((size_t)0ULL);
v___x_2782_ = lean_usize_of_nat(v___x_2771_);
v___x_2783_ = lean_unbox_uint64(v_a_2766_);
lean_dec(v_a_2766_);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2783_, v_val_2764_, v___x_2781_, v___x_2782_);
lean_dec(v_val_2764_);
v___x_2785_ = lean_box(v___x_2784_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2785_);
v___x_2787_ = v___x_2768_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v_val_2764_);
v_a_2790_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2765_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2765_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_dec(v_a_2760_);
v___x_2798_ = 1;
v___x_2799_ = lean_box(v___x_2798_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2799_);
v___x_2801_ = v___x_2762_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_a_2804_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2759_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2759_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_c_2812_);
return v_res_2823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2826_ = l_Lean_stringToMessageData(v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2827_, lean_object* v_c_x3f_2828_, lean_object* v_cs_x27_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
if (lean_obj_tag(v_cs_2827_) == 0)
{
lean_object* v___x_2841_; lean_object* v_toGoalState_2842_; lean_object* v_split_2843_; lean_object* v_mvarId_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2952_; 
v___x_2841_ = lean_st_ref_take(v_a_2830_);
v_toGoalState_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc_ref(v_toGoalState_2842_);
v_split_2843_ = lean_ctor_get(v_toGoalState_2842_, 14);
lean_inc_ref(v_split_2843_);
v_mvarId_2844_ = lean_ctor_get(v___x_2841_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2841_, 0);
lean_dec(v_unused_2953_);
v___x_2846_ = v___x_2841_;
v_isShared_2847_ = v_isSharedCheck_2952_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_mvarId_2844_);
lean_dec(v___x_2841_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2952_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v_nextDeclIdx_2848_; lean_object* v_enodeMap_2849_; lean_object* v_exprs_2850_; lean_object* v_parents_2851_; lean_object* v_congrTable_2852_; lean_object* v_appMap_2853_; lean_object* v_indicesFound_2854_; lean_object* v_toProcess_2855_; uint8_t v_inconsistent_2856_; lean_object* v_nextIdx_2857_; lean_object* v_newRawFacts_2858_; lean_object* v_facts_2859_; lean_object* v_extThms_2860_; lean_object* v_ematch_2861_; lean_object* v_inj_2862_; lean_object* v_clean_2863_; lean_object* v_sstates_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2950_; 
v_nextDeclIdx_2848_ = lean_ctor_get(v_toGoalState_2842_, 0);
v_enodeMap_2849_ = lean_ctor_get(v_toGoalState_2842_, 1);
v_exprs_2850_ = lean_ctor_get(v_toGoalState_2842_, 2);
v_parents_2851_ = lean_ctor_get(v_toGoalState_2842_, 3);
v_congrTable_2852_ = lean_ctor_get(v_toGoalState_2842_, 4);
v_appMap_2853_ = lean_ctor_get(v_toGoalState_2842_, 5);
v_indicesFound_2854_ = lean_ctor_get(v_toGoalState_2842_, 6);
v_toProcess_2855_ = lean_ctor_get(v_toGoalState_2842_, 7);
v_inconsistent_2856_ = lean_ctor_get_uint8(v_toGoalState_2842_, sizeof(void*)*17);
v_nextIdx_2857_ = lean_ctor_get(v_toGoalState_2842_, 8);
v_newRawFacts_2858_ = lean_ctor_get(v_toGoalState_2842_, 9);
v_facts_2859_ = lean_ctor_get(v_toGoalState_2842_, 10);
v_extThms_2860_ = lean_ctor_get(v_toGoalState_2842_, 11);
v_ematch_2861_ = lean_ctor_get(v_toGoalState_2842_, 12);
v_inj_2862_ = lean_ctor_get(v_toGoalState_2842_, 13);
v_clean_2863_ = lean_ctor_get(v_toGoalState_2842_, 15);
v_sstates_2864_ = lean_ctor_get(v_toGoalState_2842_, 16);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_toGoalState_2842_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v_toGoalState_2842_, 14);
lean_dec(v_unused_2951_);
v___x_2866_ = v_toGoalState_2842_;
v_isShared_2867_ = v_isSharedCheck_2950_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_sstates_2864_);
lean_inc(v_clean_2863_);
lean_inc(v_inj_2862_);
lean_inc(v_ematch_2861_);
lean_inc(v_extThms_2860_);
lean_inc(v_facts_2859_);
lean_inc(v_newRawFacts_2858_);
lean_inc(v_nextIdx_2857_);
lean_inc(v_toProcess_2855_);
lean_inc(v_indicesFound_2854_);
lean_inc(v_appMap_2853_);
lean_inc(v_congrTable_2852_);
lean_inc(v_parents_2851_);
lean_inc(v_exprs_2850_);
lean_inc(v_enodeMap_2849_);
lean_inc(v_nextDeclIdx_2848_);
lean_dec(v_toGoalState_2842_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2950_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_num_2868_; lean_object* v_added_2869_; lean_object* v_resolved_2870_; lean_object* v_trace_2871_; lean_object* v_lookaheads_2872_; lean_object* v_argPosMap_2873_; lean_object* v_argsAt_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2948_; 
v_num_2868_ = lean_ctor_get(v_split_2843_, 0);
v_added_2869_ = lean_ctor_get(v_split_2843_, 2);
v_resolved_2870_ = lean_ctor_get(v_split_2843_, 3);
v_trace_2871_ = lean_ctor_get(v_split_2843_, 4);
v_lookaheads_2872_ = lean_ctor_get(v_split_2843_, 5);
v_argPosMap_2873_ = lean_ctor_get(v_split_2843_, 6);
v_argsAt_2874_ = lean_ctor_get(v_split_2843_, 7);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_split_2843_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; 
v_unused_2949_ = lean_ctor_get(v_split_2843_, 1);
lean_dec(v_unused_2949_);
v___x_2876_ = v_split_2843_;
v_isShared_2877_ = v_isSharedCheck_2948_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_argsAt_2874_);
lean_inc(v_argPosMap_2873_);
lean_inc(v_lookaheads_2872_);
lean_inc(v_trace_2871_);
lean_inc(v_resolved_2870_);
lean_inc(v_added_2869_);
lean_inc(v_num_2868_);
lean_dec(v_split_2843_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2948_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2878_ = l_List_reverse___redArg(v_cs_x27_2829_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v___x_2878_);
v___x_2880_ = v___x_2876_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_num_2868_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_added_2869_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_resolved_2870_);
lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_trace_2871_);
lean_ctor_set(v_reuseFailAlloc_2947_, 5, v_lookaheads_2872_);
lean_ctor_set(v_reuseFailAlloc_2947_, 6, v_argPosMap_2873_);
lean_ctor_set(v_reuseFailAlloc_2947_, 7, v_argsAt_2874_);
v___x_2880_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 14, v___x_2880_);
v___x_2882_ = v___x_2866_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_nextDeclIdx_2848_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_enodeMap_2849_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_exprs_2850_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v_parents_2851_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_congrTable_2852_);
lean_ctor_set(v_reuseFailAlloc_2946_, 5, v_appMap_2853_);
lean_ctor_set(v_reuseFailAlloc_2946_, 6, v_indicesFound_2854_);
lean_ctor_set(v_reuseFailAlloc_2946_, 7, v_toProcess_2855_);
lean_ctor_set(v_reuseFailAlloc_2946_, 8, v_nextIdx_2857_);
lean_ctor_set(v_reuseFailAlloc_2946_, 9, v_newRawFacts_2858_);
lean_ctor_set(v_reuseFailAlloc_2946_, 10, v_facts_2859_);
lean_ctor_set(v_reuseFailAlloc_2946_, 11, v_extThms_2860_);
lean_ctor_set(v_reuseFailAlloc_2946_, 12, v_ematch_2861_);
lean_ctor_set(v_reuseFailAlloc_2946_, 13, v_inj_2862_);
lean_ctor_set(v_reuseFailAlloc_2946_, 14, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2946_, 15, v_clean_2863_);
lean_ctor_set(v_reuseFailAlloc_2946_, 16, v_sstates_2864_);
lean_ctor_set_uint8(v_reuseFailAlloc_2946_, sizeof(void*)*17, v_inconsistent_2856_);
v___x_2882_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2882_);
v___x_2884_ = v___x_2846_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_mvarId_2844_);
v___x_2884_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_st_ref_put(v_a_2830_, v___x_2884_);
if (lean_obj_tag(v_c_x3f_2828_) == 1)
{
lean_object* v___x_2886_; lean_object* v_toGoalState_2887_; lean_object* v_ematch_2888_; lean_object* v_mvarId_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2942_; 
v___x_2886_ = lean_st_ref_take(v_a_2830_);
v_toGoalState_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc_ref(v_toGoalState_2887_);
v_ematch_2888_ = lean_ctor_get(v_toGoalState_2887_, 12);
lean_inc_ref(v_ematch_2888_);
v_mvarId_2889_ = lean_ctor_get(v___x_2886_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2942_ == 0)
{
lean_object* v_unused_2943_; 
v_unused_2943_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2943_);
v___x_2891_ = v___x_2886_;
v_isShared_2892_ = v_isSharedCheck_2942_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_mvarId_2889_);
lean_dec(v___x_2886_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2942_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_nextDeclIdx_2893_; lean_object* v_enodeMap_2894_; lean_object* v_exprs_2895_; lean_object* v_parents_2896_; lean_object* v_congrTable_2897_; lean_object* v_appMap_2898_; lean_object* v_indicesFound_2899_; lean_object* v_toProcess_2900_; uint8_t v_inconsistent_2901_; lean_object* v_nextIdx_2902_; lean_object* v_newRawFacts_2903_; lean_object* v_facts_2904_; lean_object* v_extThms_2905_; lean_object* v_inj_2906_; lean_object* v_split_2907_; lean_object* v_clean_2908_; lean_object* v_sstates_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2940_; 
v_nextDeclIdx_2893_ = lean_ctor_get(v_toGoalState_2887_, 0);
v_enodeMap_2894_ = lean_ctor_get(v_toGoalState_2887_, 1);
v_exprs_2895_ = lean_ctor_get(v_toGoalState_2887_, 2);
v_parents_2896_ = lean_ctor_get(v_toGoalState_2887_, 3);
v_congrTable_2897_ = lean_ctor_get(v_toGoalState_2887_, 4);
v_appMap_2898_ = lean_ctor_get(v_toGoalState_2887_, 5);
v_indicesFound_2899_ = lean_ctor_get(v_toGoalState_2887_, 6);
v_toProcess_2900_ = lean_ctor_get(v_toGoalState_2887_, 7);
v_inconsistent_2901_ = lean_ctor_get_uint8(v_toGoalState_2887_, sizeof(void*)*17);
v_nextIdx_2902_ = lean_ctor_get(v_toGoalState_2887_, 8);
v_newRawFacts_2903_ = lean_ctor_get(v_toGoalState_2887_, 9);
v_facts_2904_ = lean_ctor_get(v_toGoalState_2887_, 10);
v_extThms_2905_ = lean_ctor_get(v_toGoalState_2887_, 11);
v_inj_2906_ = lean_ctor_get(v_toGoalState_2887_, 13);
v_split_2907_ = lean_ctor_get(v_toGoalState_2887_, 14);
v_clean_2908_ = lean_ctor_get(v_toGoalState_2887_, 15);
v_sstates_2909_ = lean_ctor_get(v_toGoalState_2887_, 16);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_toGoalState_2887_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v_toGoalState_2887_, 12);
lean_dec(v_unused_2941_);
v___x_2911_ = v_toGoalState_2887_;
v_isShared_2912_ = v_isSharedCheck_2940_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_sstates_2909_);
lean_inc(v_clean_2908_);
lean_inc(v_split_2907_);
lean_inc(v_inj_2906_);
lean_inc(v_extThms_2905_);
lean_inc(v_facts_2904_);
lean_inc(v_newRawFacts_2903_);
lean_inc(v_nextIdx_2902_);
lean_inc(v_toProcess_2900_);
lean_inc(v_indicesFound_2899_);
lean_inc(v_appMap_2898_);
lean_inc(v_congrTable_2897_);
lean_inc(v_parents_2896_);
lean_inc(v_exprs_2895_);
lean_inc(v_enodeMap_2894_);
lean_inc(v_nextDeclIdx_2893_);
lean_dec(v_toGoalState_2887_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2940_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_thmMap_2913_; lean_object* v_gmt_2914_; lean_object* v_thms_2915_; lean_object* v_newThms_2916_; lean_object* v_numInstances_2917_; lean_object* v_numDelayedInstances_2918_; lean_object* v_preInstances_2919_; lean_object* v_nextThmIdx_2920_; lean_object* v_matchEqNames_2921_; lean_object* v_delayedThmInsts_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2938_; 
v_thmMap_2913_ = lean_ctor_get(v_ematch_2888_, 0);
v_gmt_2914_ = lean_ctor_get(v_ematch_2888_, 1);
v_thms_2915_ = lean_ctor_get(v_ematch_2888_, 2);
v_newThms_2916_ = lean_ctor_get(v_ematch_2888_, 3);
v_numInstances_2917_ = lean_ctor_get(v_ematch_2888_, 4);
v_numDelayedInstances_2918_ = lean_ctor_get(v_ematch_2888_, 5);
v_preInstances_2919_ = lean_ctor_get(v_ematch_2888_, 7);
v_nextThmIdx_2920_ = lean_ctor_get(v_ematch_2888_, 8);
v_matchEqNames_2921_ = lean_ctor_get(v_ematch_2888_, 9);
v_delayedThmInsts_2922_ = lean_ctor_get(v_ematch_2888_, 10);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_ematch_2888_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_ematch_2888_, 6);
lean_dec(v_unused_2939_);
v___x_2924_ = v_ematch_2888_;
v_isShared_2925_ = v_isSharedCheck_2938_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_delayedThmInsts_2922_);
lean_inc(v_matchEqNames_2921_);
lean_inc(v_nextThmIdx_2920_);
lean_inc(v_preInstances_2919_);
lean_inc(v_numDelayedInstances_2918_);
lean_inc(v_numInstances_2917_);
lean_inc(v_newThms_2916_);
lean_inc(v_thms_2915_);
lean_inc(v_gmt_2914_);
lean_inc(v_thmMap_2913_);
lean_dec(v_ematch_2888_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2938_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = lean_unsigned_to_nat(0u);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 6, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_thmMap_2913_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_gmt_2914_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_thms_2915_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_newThms_2916_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_numInstances_2917_);
lean_ctor_set(v_reuseFailAlloc_2937_, 5, v_numDelayedInstances_2918_);
lean_ctor_set(v_reuseFailAlloc_2937_, 6, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2937_, 7, v_preInstances_2919_);
lean_ctor_set(v_reuseFailAlloc_2937_, 8, v_nextThmIdx_2920_);
lean_ctor_set(v_reuseFailAlloc_2937_, 9, v_matchEqNames_2921_);
lean_ctor_set(v_reuseFailAlloc_2937_, 10, v_delayedThmInsts_2922_);
v___x_2928_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 12, v___x_2928_);
v___x_2930_ = v___x_2911_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_nextDeclIdx_2893_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_enodeMap_2894_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_exprs_2895_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_parents_2896_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_congrTable_2897_);
lean_ctor_set(v_reuseFailAlloc_2936_, 5, v_appMap_2898_);
lean_ctor_set(v_reuseFailAlloc_2936_, 6, v_indicesFound_2899_);
lean_ctor_set(v_reuseFailAlloc_2936_, 7, v_toProcess_2900_);
lean_ctor_set(v_reuseFailAlloc_2936_, 8, v_nextIdx_2902_);
lean_ctor_set(v_reuseFailAlloc_2936_, 9, v_newRawFacts_2903_);
lean_ctor_set(v_reuseFailAlloc_2936_, 10, v_facts_2904_);
lean_ctor_set(v_reuseFailAlloc_2936_, 11, v_extThms_2905_);
lean_ctor_set(v_reuseFailAlloc_2936_, 12, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2936_, 13, v_inj_2906_);
lean_ctor_set(v_reuseFailAlloc_2936_, 14, v_split_2907_);
lean_ctor_set(v_reuseFailAlloc_2936_, 15, v_clean_2908_);
lean_ctor_set(v_reuseFailAlloc_2936_, 16, v_sstates_2909_);
lean_ctor_set_uint8(v_reuseFailAlloc_2936_, sizeof(void*)*17, v_inconsistent_2901_);
v___x_2930_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2932_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2930_);
v___x_2932_ = v___x_2891_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_mvarId_2889_);
v___x_2932_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_st_ref_put(v_a_2830_, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_c_x3f_2828_);
return v___x_2934_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_c_x3f_2828_);
return v___x_2944_;
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
lean_object* v_head_2954_; lean_object* v_tail_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3175_; 
v_head_2954_ = lean_ctor_get(v_cs_2827_, 0);
v_tail_2955_ = lean_ctor_get(v_cs_2827_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_cs_2827_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_2957_ = v_cs_2827_;
v_isShared_2958_ = v_isSharedCheck_3175_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_tail_2955_);
lean_inc(v_head_2954_);
lean_dec(v_cs_2827_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3175_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; uint8_t v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; uint8_t v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; uint8_t v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; uint8_t v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; uint8_t v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; uint8_t v___y_3062_; lean_object* v___y_3063_; uint8_t v___y_3064_; lean_object* v___x_3067_; 
v___x_3067_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2954_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; uint8_t v___x_3069_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = lean_unbox(v_a_3068_);
lean_dec(v_a_3068_);
if (v___x_3069_ == 0)
{
lean_del_object(v___x_2957_);
lean_dec(v_head_2954_);
v_cs_2827_ = v_tail_2955_;
goto _start;
}
else
{
lean_object* v_toCold_3071_; lean_object* v_options_3072_; lean_object* v_inheritedTraceOptions_3073_; uint8_t v_hasTrace_3074_; uint8_t v___x_3075_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; uint8_t v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3089_; uint8_t v___y_3090_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; 
v_toCold_3071_ = lean_ctor_get(v_a_2838_, 0);
v_options_3072_ = lean_ctor_get(v_toCold_3071_, 2);
v_inheritedTraceOptions_3073_ = lean_ctor_get(v_toCold_3071_, 11);
v_hasTrace_3074_ = lean_ctor_get_uint8(v_options_3072_, sizeof(void*)*1);
v___x_3075_ = 0;
if (v_hasTrace_3074_ == 0)
{
v___y_3101_ = v_a_2830_;
v___y_3102_ = v_a_2831_;
v___y_3103_ = v_a_2832_;
v___y_3104_ = v_a_2833_;
v___y_3105_ = v_a_2834_;
v___y_3106_ = v_a_2835_;
v___y_3107_ = v_a_2836_;
v___y_3108_ = v_a_2837_;
v___y_3109_ = v_a_2838_;
v___y_3110_ = v_a_2839_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3144_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3073_, v_options_3072_, v___x_3143_);
if (v___x_3144_ == 0)
{
v___y_3101_ = v_a_2830_;
v___y_3102_ = v_a_2831_;
v___y_3103_ = v_a_2832_;
v___y_3104_ = v_a_2833_;
v___y_3105_ = v_a_2834_;
v___y_3106_ = v_a_2835_;
v___y_3107_ = v_a_2836_;
v___y_3108_ = v_a_2837_;
v___y_3109_ = v_a_2838_;
v___y_3110_ = v_a_2839_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Meta_Grind_updateLastTag(v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref_known(v___x_3145_, 1);
v___x_3146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3147_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2954_);
v___x_3148_ = l_Lean_MessageData_ofExpr(v___x_3147_);
v___x_3149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3146_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3142_, v___x_3149_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_dec_ref_known(v___x_3150_, 1);
v___y_3101_ = v_a_2830_;
v___y_3102_ = v_a_2831_;
v___y_3103_ = v_a_2832_;
v___y_3104_ = v_a_2833_;
v___y_3105_ = v_a_2834_;
v___y_3106_ = v_a_2835_;
v___y_3107_ = v_a_2836_;
v___y_3108_ = v_a_2837_;
v___y_3109_ = v_a_2838_;
v___y_3110_ = v_a_2839_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3159_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3145_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3145_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
v___jp_3076_:
{
if (lean_obj_tag(v_c_x3f_2828_) == 0)
{
lean_object* v___x_3091_; 
lean_del_object(v___x_2957_);
v___x_3091_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3091_, 0, v_head_2954_);
lean_ctor_set(v___x_3091_, 1, v___y_3089_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*2, v___y_3088_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*2 + 1, v___y_3081_);
v_cs_2827_ = v_tail_2955_;
v_c_x3f_2828_ = v___x_3091_;
v_a_2830_ = v___y_3085_;
v_a_2831_ = v___y_3080_;
v_a_2832_ = v___y_3083_;
v_a_2833_ = v___y_3087_;
v_a_2834_ = v___y_3077_;
v_a_2835_ = v___y_3086_;
v_a_2836_ = v___y_3078_;
v_a_2837_ = v___y_3082_;
v_a_2838_ = v___y_3079_;
v_a_2839_ = v___y_3084_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3093_; 
v_tryPostpone_3093_ = lean_ctor_get_uint8(v_c_x3f_2828_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3093_ == 0)
{
if (v___y_3081_ == 0)
{
lean_object* v_c_3094_; lean_object* v_numCases_3095_; 
v_c_3094_ = lean_ctor_get(v_c_x3f_2828_, 0);
v_numCases_3095_ = lean_ctor_get(v_c_x3f_2828_, 1);
lean_inc_ref(v_c_3094_);
lean_inc(v_numCases_3095_);
v___y_3049_ = v___y_3077_;
v___y_3050_ = v___y_3078_;
v___y_3051_ = v___y_3079_;
v___y_3052_ = v___y_3080_;
v___y_3053_ = v___y_3081_;
v___y_3054_ = v_numCases_3095_;
v___y_3055_ = v___y_3082_;
v___y_3056_ = v___y_3083_;
v___y_3057_ = v___y_3084_;
v___y_3058_ = v___y_3085_;
v___y_3059_ = v___y_3086_;
v___y_3060_ = v___y_3087_;
v___y_3061_ = v_c_3094_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3089_;
v___y_3064_ = v___x_3075_;
goto v___jp_3048_;
}
else
{
lean_dec(v___y_3089_);
v___y_2960_ = v___y_3086_;
v___y_2961_ = v___y_3077_;
v___y_2962_ = v___y_3078_;
v___y_2963_ = v___y_3079_;
v___y_2964_ = v___y_3080_;
v___y_2965_ = v___y_3087_;
v___y_2966_ = v___y_3082_;
v___y_2967_ = v___y_3084_;
v___y_2968_ = v___y_3083_;
v___y_2969_ = v___y_3085_;
goto v___jp_2959_;
}
}
else
{
if (v___y_3081_ == 0)
{
lean_object* v_c_3096_; 
lean_del_object(v___x_2957_);
v_c_3096_ = lean_ctor_get(v_c_x3f_2828_, 0);
lean_inc_ref(v_c_3096_);
lean_dec_ref_known(v_c_x3f_2828_, 2);
v___y_2975_ = v___y_3077_;
v___y_2976_ = v___y_3078_;
v___y_2977_ = v___y_3079_;
v___y_2978_ = v___y_3080_;
v___y_2979_ = v___y_3081_;
v___y_2980_ = v___y_3082_;
v___y_2981_ = v___y_3084_;
v___y_2982_ = v___y_3083_;
v___y_2983_ = v___y_3085_;
v___y_2984_ = v___y_3086_;
v___y_2985_ = v___y_3087_;
v___y_2986_ = v_c_3096_;
v___y_2987_ = v___y_3088_;
v___y_2988_ = v___y_3089_;
goto v___jp_2974_;
}
else
{
if (v___y_3090_ == 0)
{
lean_object* v_c_3097_; lean_object* v_numCases_3098_; 
v_c_3097_ = lean_ctor_get(v_c_x3f_2828_, 0);
v_numCases_3098_ = lean_ctor_get(v_c_x3f_2828_, 1);
lean_inc_ref(v_c_3097_);
lean_inc(v_numCases_3098_);
v___y_3049_ = v___y_3077_;
v___y_3050_ = v___y_3078_;
v___y_3051_ = v___y_3079_;
v___y_3052_ = v___y_3080_;
v___y_3053_ = v___y_3081_;
v___y_3054_ = v_numCases_3098_;
v___y_3055_ = v___y_3082_;
v___y_3056_ = v___y_3083_;
v___y_3057_ = v___y_3084_;
v___y_3058_ = v___y_3085_;
v___y_3059_ = v___y_3086_;
v___y_3060_ = v___y_3087_;
v___y_3061_ = v_c_3097_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3089_;
v___y_3064_ = v___y_3090_;
goto v___jp_3048_;
}
else
{
lean_object* v_c_3099_; 
lean_del_object(v___x_2957_);
v_c_3099_ = lean_ctor_get(v_c_x3f_2828_, 0);
lean_inc_ref(v_c_3099_);
lean_dec_ref_known(v_c_x3f_2828_, 2);
v___y_2975_ = v___y_3077_;
v___y_2976_ = v___y_3078_;
v___y_2977_ = v___y_3079_;
v___y_2978_ = v___y_3080_;
v___y_2979_ = v___y_3081_;
v___y_2980_ = v___y_3082_;
v___y_2981_ = v___y_3084_;
v___y_2982_ = v___y_3083_;
v___y_2983_ = v___y_3085_;
v___y_2984_ = v___y_3086_;
v___y_2985_ = v___y_3087_;
v___y_2986_ = v_c_3099_;
v___y_2987_ = v___y_3088_;
v___y_2988_ = v___y_3089_;
goto v___jp_2974_;
}
}
}
}
}
v___jp_3100_:
{
lean_object* v___x_3111_; 
lean_inc(v_head_2954_);
v___x_3111_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2954_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
switch(lean_obj_tag(v_a_3112_))
{
case 0:
{
lean_del_object(v___x_2957_);
lean_dec(v_head_2954_);
v_cs_2827_ = v_tail_2955_;
v_a_2830_ = v___y_3101_;
v_a_2831_ = v___y_3102_;
v_a_2832_ = v___y_3103_;
v_a_2833_ = v___y_3104_;
v_a_2834_ = v___y_3105_;
v_a_2835_ = v___y_3106_;
v_a_2836_ = v___y_3107_;
v_a_2837_ = v___y_3108_;
v_a_2838_ = v___y_3109_;
v_a_2839_ = v___y_3110_;
goto _start;
}
case 1:
{
lean_object* v___x_3114_; 
lean_del_object(v___x_2957_);
v___x_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_head_2954_);
lean_ctor_set(v___x_3114_, 1, v_cs_x27_2829_);
v_cs_2827_ = v_tail_2955_;
v_cs_x27_2829_ = v___x_3114_;
v_a_2830_ = v___y_3101_;
v_a_2831_ = v___y_3102_;
v_a_2832_ = v___y_3103_;
v_a_2833_ = v___y_3104_;
v_a_2834_ = v___y_3105_;
v_a_2835_ = v___y_3106_;
v_a_2836_ = v___y_3107_;
v_a_2837_ = v___y_3108_;
v_a_2838_ = v___y_3109_;
v_a_2839_ = v___y_3110_;
goto _start;
}
default: 
{
lean_object* v_numCases_3116_; uint8_t v_isRec_3117_; uint8_t v_tryPostpone_3118_; lean_object* v___x_3119_; 
v_numCases_3116_ = lean_ctor_get(v_a_3112_, 0);
lean_inc(v_numCases_3116_);
v_isRec_3117_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*1);
v_tryPostpone_3118_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3112_, 1);
v___x_3119_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3103_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; uint8_t v___x_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = lean_unbox(v_a_3120_);
lean_dec(v_a_3120_);
if (v___x_3121_ == 0)
{
v___y_3077_ = v___y_3105_;
v___y_3078_ = v___y_3107_;
v___y_3079_ = v___y_3109_;
v___y_3080_ = v___y_3102_;
v___y_3081_ = v_tryPostpone_3118_;
v___y_3082_ = v___y_3108_;
v___y_3083_ = v___y_3103_;
v___y_3084_ = v___y_3110_;
v___y_3085_ = v___y_3101_;
v___y_3086_ = v___y_3106_;
v___y_3087_ = v___y_3104_;
v___y_3088_ = v_isRec_3117_;
v___y_3089_ = v_numCases_3116_;
v___y_3090_ = v___x_3075_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = lean_unsigned_to_nat(1u);
v___x_3123_ = lean_nat_dec_lt(v___x_3122_, v_numCases_3116_);
if (v___x_3123_ == 0)
{
v___y_3077_ = v___y_3105_;
v___y_3078_ = v___y_3107_;
v___y_3079_ = v___y_3109_;
v___y_3080_ = v___y_3102_;
v___y_3081_ = v_tryPostpone_3118_;
v___y_3082_ = v___y_3108_;
v___y_3083_ = v___y_3103_;
v___y_3084_ = v___y_3110_;
v___y_3085_ = v___y_3101_;
v___y_3086_ = v___y_3106_;
v___y_3087_ = v___y_3104_;
v___y_3088_ = v_isRec_3117_;
v___y_3089_ = v_numCases_3116_;
v___y_3090_ = v___x_3123_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3124_; 
lean_dec(v_numCases_3116_);
lean_del_object(v___x_2957_);
v___x_3124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3124_, 0, v_head_2954_);
lean_ctor_set(v___x_3124_, 1, v_cs_x27_2829_);
v_cs_2827_ = v_tail_2955_;
v_cs_x27_2829_ = v___x_3124_;
v_a_2830_ = v___y_3101_;
v_a_2831_ = v___y_3102_;
v_a_2832_ = v___y_3103_;
v_a_2833_ = v___y_3104_;
v_a_2834_ = v___y_3105_;
v_a_2835_ = v___y_3106_;
v_a_2836_ = v___y_3107_;
v_a_2837_ = v___y_3108_;
v_a_2838_ = v___y_3109_;
v_a_2839_ = v___y_3110_;
goto _start;
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_numCases_3116_);
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3126_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3119_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3119_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3134_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3111_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3111_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3167_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3067_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3067_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
v___jp_2959_:
{
lean_object* v___x_2971_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v_cs_x27_2829_);
v___x_2971_ = v___x_2957_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_head_2954_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_cs_x27_2829_);
v___x_2971_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
v_cs_2827_ = v_tail_2955_;
v_cs_x27_2829_ = v___x_2971_;
v_a_2830_ = v___y_2969_;
v_a_2831_ = v___y_2964_;
v_a_2832_ = v___y_2968_;
v_a_2833_ = v___y_2965_;
v_a_2834_ = v___y_2961_;
v_a_2835_ = v___y_2960_;
v_a_2836_ = v___y_2962_;
v_a_2837_ = v___y_2966_;
v_a_2838_ = v___y_2963_;
v_a_2839_ = v___y_2967_;
goto _start;
}
}
v___jp_2974_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2989_, 0, v_head_2954_);
lean_ctor_set(v___x_2989_, 1, v___y_2988_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*2, v___y_2987_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*2 + 1, v___y_2979_);
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___y_2986_);
lean_ctor_set(v___x_2990_, 1, v_cs_x27_2829_);
v_cs_2827_ = v_tail_2955_;
v_c_x3f_2828_ = v___x_2989_;
v_cs_x27_2829_ = v___x_2990_;
v_a_2830_ = v___y_2983_;
v_a_2831_ = v___y_2978_;
v_a_2832_ = v___y_2982_;
v_a_2833_ = v___y_2985_;
v_a_2834_ = v___y_2975_;
v_a_2835_ = v___y_2984_;
v_a_2836_ = v___y_2976_;
v_a_2837_ = v___y_2980_;
v_a_2838_ = v___y_2977_;
v_a_2839_ = v___y_2981_;
goto _start;
}
v___jp_2992_:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2954_, v___y_3002_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3005_, v___y_3002_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; uint8_t v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = lean_nat_dec_lt(v_a_3009_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec(v_a_3009_);
if (v___x_3012_ == 0)
{
uint8_t v___x_3013_; 
v___x_3013_ = lean_nat_dec_lt(v___y_3007_, v___y_2998_);
lean_dec(v___y_2998_);
if (v___x_3013_ == 0)
{
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3005_);
v___y_2960_ = v___y_3003_;
v___y_2961_ = v___y_2993_;
v___y_2962_ = v___y_2994_;
v___y_2963_ = v___y_2995_;
v___y_2964_ = v___y_2996_;
v___y_2965_ = v___y_3004_;
v___y_2966_ = v___y_2999_;
v___y_2967_ = v___y_3001_;
v___y_2968_ = v___y_3000_;
v___y_2969_ = v___y_3002_;
goto v___jp_2959_;
}
else
{
lean_del_object(v___x_2957_);
lean_dec(v_c_x3f_2828_);
v___y_2975_ = v___y_2993_;
v___y_2976_ = v___y_2994_;
v___y_2977_ = v___y_2995_;
v___y_2978_ = v___y_2996_;
v___y_2979_ = v___y_2997_;
v___y_2980_ = v___y_2999_;
v___y_2981_ = v___y_3001_;
v___y_2982_ = v___y_3000_;
v___y_2983_ = v___y_3002_;
v___y_2984_ = v___y_3003_;
v___y_2985_ = v___y_3004_;
v___y_2986_ = v___y_3005_;
v___y_2987_ = v___y_3006_;
v___y_2988_ = v___y_3007_;
goto v___jp_2974_;
}
}
else
{
lean_dec(v___y_2998_);
lean_del_object(v___x_2957_);
lean_dec(v_c_x3f_2828_);
v___y_2975_ = v___y_2993_;
v___y_2976_ = v___y_2994_;
v___y_2977_ = v___y_2995_;
v___y_2978_ = v___y_2996_;
v___y_2979_ = v___y_2997_;
v___y_2980_ = v___y_2999_;
v___y_2981_ = v___y_3001_;
v___y_2982_ = v___y_3000_;
v___y_2983_ = v___y_3002_;
v___y_2984_ = v___y_3003_;
v___y_2985_ = v___y_3004_;
v___y_2986_ = v___y_3005_;
v___y_2987_ = v___y_3006_;
v___y_2988_ = v___y_3007_;
goto v___jp_2974_;
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_3009_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_2998_);
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3014_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3010_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3010_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_2998_);
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_dec(v_cs_x27_2829_);
lean_dec(v_c_x3f_2828_);
v_a_3022_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3008_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3008_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
v___jp_3030_:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(1u);
v___x_3047_ = lean_nat_dec_lt(v___x_3046_, v___y_3036_);
if (v___x_3047_ == 0)
{
v___y_2993_ = v___y_3031_;
v___y_2994_ = v___y_3032_;
v___y_2995_ = v___y_3033_;
v___y_2996_ = v___y_3034_;
v___y_2997_ = v___y_3035_;
v___y_2998_ = v___y_3036_;
v___y_2999_ = v___y_3037_;
v___y_3000_ = v___y_3038_;
v___y_3001_ = v___y_3039_;
v___y_3002_ = v___y_3040_;
v___y_3003_ = v___y_3041_;
v___y_3004_ = v___y_3042_;
v___y_3005_ = v___y_3043_;
v___y_3006_ = v___y_3044_;
v___y_3007_ = v___y_3045_;
goto v___jp_2992_;
}
else
{
lean_dec(v___y_3036_);
lean_del_object(v___x_2957_);
lean_dec(v_c_x3f_2828_);
v___y_2975_ = v___y_3031_;
v___y_2976_ = v___y_3032_;
v___y_2977_ = v___y_3033_;
v___y_2978_ = v___y_3034_;
v___y_2979_ = v___y_3035_;
v___y_2980_ = v___y_3037_;
v___y_2981_ = v___y_3039_;
v___y_2982_ = v___y_3038_;
v___y_2983_ = v___y_3040_;
v___y_2984_ = v___y_3041_;
v___y_2985_ = v___y_3042_;
v___y_2986_ = v___y_3043_;
v___y_2987_ = v___y_3044_;
v___y_2988_ = v___y_3045_;
goto v___jp_2974_;
}
}
v___jp_3048_:
{
lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3065_ = lean_unsigned_to_nat(1u);
v___x_3066_ = lean_nat_dec_eq(v___y_3063_, v___x_3065_);
if (v___x_3066_ == 0)
{
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3052_;
v___y_2997_ = v___y_3053_;
v___y_2998_ = v___y_3054_;
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3056_;
v___y_3001_ = v___y_3057_;
v___y_3002_ = v___y_3058_;
v___y_3003_ = v___y_3059_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3061_;
v___y_3006_ = v___y_3062_;
v___y_3007_ = v___y_3063_;
goto v___jp_2992_;
}
else
{
if (v___y_3062_ == 0)
{
v___y_3031_ = v___y_3049_;
v___y_3032_ = v___y_3050_;
v___y_3033_ = v___y_3051_;
v___y_3034_ = v___y_3052_;
v___y_3035_ = v___y_3053_;
v___y_3036_ = v___y_3054_;
v___y_3037_ = v___y_3055_;
v___y_3038_ = v___y_3056_;
v___y_3039_ = v___y_3057_;
v___y_3040_ = v___y_3058_;
v___y_3041_ = v___y_3059_;
v___y_3042_ = v___y_3060_;
v___y_3043_ = v___y_3061_;
v___y_3044_ = v___y_3062_;
v___y_3045_ = v___y_3063_;
goto v___jp_3030_;
}
else
{
if (v___y_3064_ == 0)
{
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3052_;
v___y_2997_ = v___y_3053_;
v___y_2998_ = v___y_3054_;
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3056_;
v___y_3001_ = v___y_3057_;
v___y_3002_ = v___y_3058_;
v___y_3003_ = v___y_3059_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3061_;
v___y_3006_ = v___y_3062_;
v___y_3007_ = v___y_3063_;
goto v___jp_2992_;
}
else
{
v___y_3031_ = v___y_3049_;
v___y_3032_ = v___y_3050_;
v___y_3033_ = v___y_3051_;
v___y_3034_ = v___y_3052_;
v___y_3035_ = v___y_3053_;
v___y_3036_ = v___y_3054_;
v___y_3037_ = v___y_3055_;
v___y_3038_ = v___y_3056_;
v___y_3039_ = v___y_3057_;
v___y_3040_ = v___y_3058_;
v___y_3041_ = v___y_3059_;
v___y_3042_ = v___y_3060_;
v___y_3043_ = v___y_3061_;
v___y_3044_ = v___y_3062_;
v___y_3045_ = v___y_3063_;
goto v___jp_3030_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3176_, lean_object* v_c_x3f_3177_, lean_object* v_cs_x27_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3176_, v_c_x3f_3177_, v_cs_x27_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec(v_a_3179_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3191_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3238_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3238_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3238_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_unbox(v_a_3203_);
lean_dec(v_a_3203_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
lean_del_object(v___x_3205_);
v___x_3208_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3191_, v_a_3193_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3225_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3225_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3225_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_unbox(v_a_3209_);
lean_dec(v_a_3209_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v_toGoalState_3215_; lean_object* v_split_3216_; lean_object* v_candidates_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_del_object(v___x_3211_);
v___x_3214_ = lean_st_ref_get(v_a_3191_);
v_toGoalState_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_toGoalState_3215_);
lean_dec(v___x_3214_);
v_split_3216_ = lean_ctor_get(v_toGoalState_3215_, 14);
lean_inc_ref(v_split_3216_);
lean_dec_ref(v_toGoalState_3215_);
v_candidates_3217_ = lean_ctor_get(v_split_3216_, 1);
lean_inc(v_candidates_3217_);
lean_dec_ref(v_split_3216_);
v___x_3218_ = lean_box(0);
v___x_3219_ = lean_box(0);
v___x_3220_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3217_, v___x_3218_, v___x_3219_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3221_ = lean_box(0);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3221_);
v___x_3223_ = v___x_3211_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_a_3226_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3208_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3208_);
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
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_box(0);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3234_);
v___x_3236_ = v___x_3205_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
v_a_3239_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3202_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3202_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec(v_a_3247_);
return v_res_3258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_box(0);
v___x_3267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3268_ = l_Lean_mkConst(v___x_3267_, v___x_3266_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3269_){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3271_ = l_Lean_Expr_app___override(v___x_3270_, v_c_3269_);
return v___x_3271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_box(0);
v___x_3281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3282_ = l_Lean_mkConst(v___x_3281_, v___x_3280_);
return v___x_3282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_box(0);
v___x_3289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3290_ = l_Lean_mkConst(v___x_3289_, v___x_3288_);
return v___x_3290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3298_ = l_Lean_mkConst(v___x_3297_, v___x_3296_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___x_3371_; 
lean_inc_ref(v_c_3299_);
v___x_3371_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3299_, v_a_3307_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3444_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3444_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3444_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; uint8_t v___x_3377_; 
v___x_3376_ = l_Lean_Expr_cleanupAnnotations(v_a_3372_);
v___x_3377_ = l_Lean_Expr_isApp(v___x_3376_);
if (v___x_3377_ == 0)
{
lean_dec_ref(v___x_3376_);
lean_del_object(v___x_3374_);
v___y_3359_ = v_a_3300_;
v___y_3360_ = v_a_3301_;
v___y_3361_ = v_a_3302_;
v___y_3362_ = v_a_3303_;
v___y_3363_ = v_a_3304_;
v___y_3364_ = v_a_3305_;
v___y_3365_ = v_a_3306_;
v___y_3366_ = v_a_3307_;
v___y_3367_ = v_a_3308_;
v___y_3368_ = v_a_3309_;
goto v___jp_3358_;
}
else
{
lean_object* v_arg_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v_arg_3378_ = lean_ctor_get(v___x_3376_, 1);
lean_inc_ref(v_arg_3378_);
v___x_3379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3376_);
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3381_ = l_Lean_Expr_isConstOf(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
uint8_t v___x_3382_; 
v___x_3382_ = l_Lean_Expr_isApp(v___x_3379_);
if (v___x_3382_ == 0)
{
lean_dec_ref(v___x_3379_);
lean_dec_ref(v_arg_3378_);
lean_del_object(v___x_3374_);
v___y_3359_ = v_a_3300_;
v___y_3360_ = v_a_3301_;
v___y_3361_ = v_a_3302_;
v___y_3362_ = v_a_3303_;
v___y_3363_ = v_a_3304_;
v___y_3364_ = v_a_3305_;
v___y_3365_ = v_a_3306_;
v___y_3366_ = v_a_3307_;
v___y_3367_ = v_a_3308_;
v___y_3368_ = v_a_3309_;
goto v___jp_3358_;
}
else
{
lean_object* v_arg_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_arg_3383_ = lean_ctor_get(v___x_3379_, 1);
lean_inc_ref(v_arg_3383_);
v___x_3384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3379_);
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3386_ = l_Lean_Expr_isConstOf(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
uint8_t v___x_3387_; 
v___x_3387_ = l_Lean_Expr_isApp(v___x_3384_);
if (v___x_3387_ == 0)
{
lean_dec_ref(v___x_3384_);
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
lean_del_object(v___x_3374_);
v___y_3359_ = v_a_3300_;
v___y_3360_ = v_a_3301_;
v___y_3361_ = v_a_3302_;
v___y_3362_ = v_a_3303_;
v___y_3363_ = v_a_3304_;
v___y_3364_ = v_a_3305_;
v___y_3365_ = v_a_3306_;
v___y_3366_ = v_a_3307_;
v___y_3367_ = v_a_3308_;
v___y_3368_ = v_a_3309_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3384_);
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3390_ = l_Lean_Expr_isConstOf(v___x_3388_, v___x_3389_);
lean_dec_ref(v___x_3388_);
if (v___x_3390_ == 0)
{
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
lean_del_object(v___x_3374_);
v___y_3359_ = v_a_3300_;
v___y_3360_ = v_a_3301_;
v___y_3361_ = v_a_3302_;
v___y_3362_ = v_a_3303_;
v___y_3363_ = v_a_3304_;
v___y_3364_ = v_a_3305_;
v___y_3365_ = v_a_3306_;
v___y_3366_ = v_a_3307_;
v___y_3367_ = v_a_3308_;
v___y_3368_ = v_a_3309_;
goto v___jp_3358_;
}
else
{
uint8_t v___x_3391_; 
lean_inc_ref(v_c_3299_);
v___x_3391_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3299_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
v___x_3392_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3299_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3392_);
v___x_3394_ = v___x_3374_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
else
{
lean_object* v___x_3396_; 
lean_del_object(v___x_3374_);
lean_inc_ref(v_c_3299_);
v___x_3396_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3299_, v_a_3300_, v_a_3304_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; uint8_t v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v___x_3398_ = lean_unbox(v_a_3397_);
lean_dec(v_a_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3409_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3409_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3409_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3405_ = l_Lean_mkApp3(v___x_3404_, v_arg_3383_, v_arg_3378_, v_a_3400_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3405_);
v___x_3407_ = v___x_3402_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
else
{
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
return v___x_3399_;
}
}
else
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3420_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3420_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3420_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3416_ = l_Lean_mkApp3(v___x_3415_, v_arg_3383_, v_arg_3378_, v_a_3411_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3416_);
v___x_3418_ = v___x_3413_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
return v___x_3410_;
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
lean_dec_ref(v_c_3299_);
v_a_3421_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3396_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3396_);
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
lean_object* v___x_3429_; 
lean_dec_ref(v___x_3384_);
lean_del_object(v___x_3374_);
v___x_3429_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
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
v___x_3434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3435_ = l_Lean_mkApp3(v___x_3434_, v_arg_3383_, v_arg_3378_, v_a_3430_);
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
lean_dec_ref(v_arg_3383_);
lean_dec_ref(v_arg_3378_);
return v___x_3429_;
}
}
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec_ref(v___x_3379_);
lean_dec_ref(v_c_3299_);
v___x_3440_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3378_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3440_);
v___x_3442_ = v___x_3374_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3299_);
return v___x_3371_;
}
v___jp_3311_:
{
if (v___y_3322_ == 0)
{
lean_object* v___x_3323_; 
lean_inc_ref(v_c_3299_);
v___x_3323_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3299_, v___y_3314_, v___y_3318_, v___y_3321_, v___y_3313_, v___y_3317_, v___y_3320_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3342_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3342_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3342_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
uint8_t v___x_3328_; 
v___x_3328_ = lean_unbox(v_a_3324_);
lean_dec(v_a_3324_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3330_; 
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v_c_3299_);
v___x_3330_ = v___x_3326_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_c_3299_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
else
{
lean_object* v___x_3332_; 
lean_del_object(v___x_3326_);
lean_inc_ref(v_c_3299_);
v___x_3332_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3299_, v___y_3314_, v___y_3319_, v___y_3316_, v___y_3312_, v___y_3318_, v___y_3315_, v___y_3321_, v___y_3313_, v___y_3317_, v___y_3320_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3341_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3299_, v_a_3333_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3337_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_dec_ref(v_c_3299_);
return v___x_3332_;
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref(v_c_3299_);
v_a_3343_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3323_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3323_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3351_ = lean_unsigned_to_nat(1u);
v___x_3352_ = l_Lean_Expr_getAppNumArgs(v_c_3299_);
v___x_3353_ = lean_nat_sub(v___x_3352_, v___x_3351_);
lean_dec(v___x_3352_);
v___x_3354_ = lean_nat_sub(v___x_3353_, v___x_3351_);
lean_dec(v___x_3353_);
v___x_3355_ = l_Lean_Expr_getRevArg_x21(v_c_3299_, v___x_3354_);
lean_dec_ref(v_c_3299_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3355_);
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
return v___x_3357_;
}
}
v___jp_3358_:
{
uint8_t v___x_3369_; 
v___x_3369_ = l_Lean_Meta_Grind_isIte(v_c_3299_);
if (v___x_3369_ == 0)
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_Meta_Grind_isDIte(v_c_3299_);
v___y_3312_ = v___y_3362_;
v___y_3313_ = v___y_3366_;
v___y_3314_ = v___y_3359_;
v___y_3315_ = v___y_3364_;
v___y_3316_ = v___y_3361_;
v___y_3317_ = v___y_3367_;
v___y_3318_ = v___y_3363_;
v___y_3319_ = v___y_3360_;
v___y_3320_ = v___y_3368_;
v___y_3321_ = v___y_3365_;
v___y_3322_ = v___x_3370_;
goto v___jp_3311_;
}
else
{
v___y_3312_ = v___y_3362_;
v___y_3313_ = v___y_3366_;
v___y_3314_ = v___y_3359_;
v___y_3315_ = v___y_3364_;
v___y_3316_ = v___y_3361_;
v___y_3317_ = v___y_3367_;
v___y_3318_ = v___y_3363_;
v___y_3319_ = v___y_3360_;
v___y_3320_ = v___y_3368_;
v___y_3321_ = v___y_3365_;
v___y_3322_ = v___x_3369_;
goto v___jp_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec(v_a_3446_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3458_, lean_object* v_major_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3460_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; uint8_t v_trace_3469_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v_trace_3469_ = lean_ctor_get_uint8(v_a_3468_, sizeof(void*)*14);
lean_dec(v_a_3468_);
if (v_trace_3469_ == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Meta_Grind_cases(v_mvarId_3458_, v_major_3459_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; 
lean_inc(v_a_3465_);
lean_inc_ref(v_a_3464_);
lean_inc(v_a_3463_);
lean_inc_ref(v_a_3462_);
lean_inc_ref(v_major_3459_);
v___x_3471_ = lean_infer_type(v_major_3459_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = l_Lean_Meta_whnfD(v_a_3472_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3475_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___x_3475_ = l_Lean_Expr_getAppFn(v_a_3474_);
lean_dec(v_a_3474_);
if (lean_obj_tag(v___x_3475_) == 4)
{
lean_object* v_declName_3476_; lean_object* v___x_3477_; 
v_declName_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_declName_3476_);
lean_dec_ref_known(v___x_3475_, 2);
v___x_3477_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3476_, v_a_3461_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3478_; 
lean_dec_ref_known(v___x_3477_, 1);
v___x_3478_ = l_Lean_Meta_Grind_cases(v_mvarId_3458_, v_major_3459_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
return v___x_3478_;
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v_major_3459_);
lean_dec(v_mvarId_3458_);
v_a_3479_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3477_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3477_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v___x_3487_; 
lean_dec_ref(v___x_3475_);
v___x_3487_ = l_Lean_Meta_Grind_cases(v_mvarId_3458_, v_major_3459_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
return v___x_3487_;
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref(v_major_3459_);
lean_dec(v_mvarId_3458_);
v_a_3488_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3473_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3473_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_major_3459_);
lean_dec(v_mvarId_3458_);
v_a_3496_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3471_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3471_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_major_3459_);
lean_dec(v_mvarId_3458_);
v_a_3504_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3467_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3467_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3512_, lean_object* v_major_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3512_, v_major_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3522_, lean_object* v_major_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3522_, v_major_3523_, v_a_3526_, v_a_3527_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3536_, lean_object* v_major_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3536_, v_major_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec(v_a_3538_);
return v_res_3549_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3550_){
_start:
{
uint64_t v_anchor_3551_; 
v_anchor_3551_ = lean_ctor_get_uint64(v_e_3550_, sizeof(void*)*3);
return v_anchor_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3552_){
_start:
{
uint64_t v_res_3553_; lean_object* v_r_3554_; 
v_res_3553_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3552_);
lean_dec_ref(v_e_3552_);
v_r_3554_ = lean_box_uint64(v_res_3553_);
return v_r_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3557_, lean_object* v_x_3558_){
_start:
{
if (lean_obj_tag(v_x_3558_) == 0)
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_box(0);
return v___x_3559_;
}
else
{
lean_object* v_key_3560_; lean_object* v_value_3561_; lean_object* v_tail_3562_; uint64_t v___x_3563_; uint8_t v___x_3564_; 
v_key_3560_ = lean_ctor_get(v_x_3558_, 0);
v_value_3561_ = lean_ctor_get(v_x_3558_, 1);
v_tail_3562_ = lean_ctor_get(v_x_3558_, 2);
v___x_3563_ = lean_unbox_uint64(v_key_3560_);
v___x_3564_ = lean_uint64_dec_eq(v___x_3563_, v_a_3557_);
if (v___x_3564_ == 0)
{
v_x_3558_ = v_tail_3562_;
goto _start;
}
else
{
lean_object* v___x_3566_; 
lean_inc(v_value_3561_);
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_value_3561_);
return v___x_3566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3567_, lean_object* v_x_3568_){
_start:
{
uint64_t v_a_boxed_3569_; lean_object* v_res_3570_; 
v_a_boxed_3569_ = lean_unbox_uint64(v_a_3567_);
lean_dec_ref(v_a_3567_);
v_res_3570_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3569_, v_x_3568_);
lean_dec(v_x_3568_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3571_, uint64_t v_a_3572_){
_start:
{
lean_object* v_buckets_3573_; lean_object* v___x_3574_; uint64_t v___x_3575_; uint64_t v___x_3576_; uint64_t v_fold_3577_; uint64_t v___x_3578_; uint64_t v___x_3579_; uint64_t v___x_3580_; size_t v___x_3581_; size_t v___x_3582_; size_t v___x_3583_; size_t v___x_3584_; size_t v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_buckets_3573_ = lean_ctor_get(v_m_3571_, 1);
v___x_3574_ = lean_array_get_size(v_buckets_3573_);
v___x_3575_ = 32ULL;
v___x_3576_ = lean_uint64_shift_right(v_a_3572_, v___x_3575_);
v_fold_3577_ = lean_uint64_xor(v_a_3572_, v___x_3576_);
v___x_3578_ = 16ULL;
v___x_3579_ = lean_uint64_shift_right(v_fold_3577_, v___x_3578_);
v___x_3580_ = lean_uint64_xor(v_fold_3577_, v___x_3579_);
v___x_3581_ = lean_uint64_to_usize(v___x_3580_);
v___x_3582_ = lean_usize_of_nat(v___x_3574_);
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_sub(v___x_3582_, v___x_3583_);
v___x_3585_ = lean_usize_land(v___x_3581_, v___x_3584_);
v___x_3586_ = lean_array_uget_borrowed(v_buckets_3573_, v___x_3585_);
v___x_3587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3572_, v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3588_, lean_object* v_a_3589_){
_start:
{
uint64_t v_a_boxed_3590_; lean_object* v_res_3591_; 
v_a_boxed_3590_ = lean_unbox_uint64(v_a_3589_);
lean_dec_ref(v_a_3589_);
v_res_3591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3588_, v_a_boxed_3590_);
lean_dec_ref(v_m_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
if (lean_obj_tag(v_x_3593_) == 0)
{
return v_x_3592_;
}
else
{
lean_object* v_key_3594_; lean_object* v_value_3595_; lean_object* v_tail_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3620_; 
v_key_3594_ = lean_ctor_get(v_x_3593_, 0);
v_value_3595_ = lean_ctor_get(v_x_3593_, 1);
v_tail_3596_ = lean_ctor_get(v_x_3593_, 2);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_x_3593_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3598_ = v_x_3593_;
v_isShared_3599_ = v_isSharedCheck_3620_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_tail_3596_);
lean_inc(v_value_3595_);
lean_inc(v_key_3594_);
lean_dec(v_x_3593_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3620_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; uint64_t v___x_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; uint64_t v_fold_3605_; uint64_t v___x_3606_; uint64_t v___x_3607_; uint64_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3616_; 
v___x_3600_ = lean_array_get_size(v_x_3592_);
v___x_3601_ = 32ULL;
v___x_3602_ = lean_unbox_uint64(v_key_3594_);
v___x_3603_ = lean_uint64_shift_right(v___x_3602_, v___x_3601_);
v___x_3604_ = lean_unbox_uint64(v_key_3594_);
v_fold_3605_ = lean_uint64_xor(v___x_3604_, v___x_3603_);
v___x_3606_ = 16ULL;
v___x_3607_ = lean_uint64_shift_right(v_fold_3605_, v___x_3606_);
v___x_3608_ = lean_uint64_xor(v_fold_3605_, v___x_3607_);
v___x_3609_ = lean_uint64_to_usize(v___x_3608_);
v___x_3610_ = lean_usize_of_nat(v___x_3600_);
v___x_3611_ = ((size_t)1ULL);
v___x_3612_ = lean_usize_sub(v___x_3610_, v___x_3611_);
v___x_3613_ = lean_usize_land(v___x_3609_, v___x_3612_);
v___x_3614_ = lean_array_uget_borrowed(v_x_3592_, v___x_3613_);
lean_inc(v___x_3614_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 2, v___x_3614_);
v___x_3616_ = v___x_3598_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_key_3594_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_value_3595_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_array_uset(v_x_3592_, v___x_3613_, v___x_3616_);
v_x_3592_ = v___x_3617_;
v_x_3593_ = v_tail_3596_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3621_, lean_object* v_source_3622_, lean_object* v_target_3623_){
_start:
{
lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3624_ = lean_array_get_size(v_source_3622_);
v___x_3625_ = lean_nat_dec_lt(v_i_3621_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_dec_ref(v_source_3622_);
lean_dec(v_i_3621_);
return v_target_3623_;
}
else
{
lean_object* v_es_3626_; lean_object* v___x_3627_; lean_object* v_source_3628_; lean_object* v_target_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v_es_3626_ = lean_array_fget(v_source_3622_, v_i_3621_);
v___x_3627_ = lean_box(0);
v_source_3628_ = lean_array_fset(v_source_3622_, v_i_3621_, v___x_3627_);
v_target_3629_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3623_, v_es_3626_);
v___x_3630_ = lean_unsigned_to_nat(1u);
v___x_3631_ = lean_nat_add(v_i_3621_, v___x_3630_);
lean_dec(v_i_3621_);
v_i_3621_ = v___x_3631_;
v_source_3622_ = v_source_3628_;
v_target_3623_ = v_target_3629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3633_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v_nbuckets_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3634_ = lean_array_get_size(v_data_3633_);
v___x_3635_ = lean_unsigned_to_nat(2u);
v_nbuckets_3636_ = lean_nat_mul(v___x_3634_, v___x_3635_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = lean_box(0);
v___x_3639_ = lean_mk_array(v_nbuckets_3636_, v___x_3638_);
v___x_3640_ = lean_array_propagate_mark(v_data_3633_, v___x_3639_);
v___x_3641_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3637_, v_data_3633_, v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3642_, lean_object* v_b_3643_, lean_object* v_x_3644_){
_start:
{
if (lean_obj_tag(v_x_3644_) == 0)
{
lean_dec(v_b_3643_);
return v_x_3644_;
}
else
{
lean_object* v_key_3645_; lean_object* v_value_3646_; lean_object* v_tail_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3661_; 
v_key_3645_ = lean_ctor_get(v_x_3644_, 0);
v_value_3646_ = lean_ctor_get(v_x_3644_, 1);
v_tail_3647_ = lean_ctor_get(v_x_3644_, 2);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_x_3644_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3649_ = v_x_3644_;
v_isShared_3650_ = v_isSharedCheck_3661_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_tail_3647_);
lean_inc(v_value_3646_);
lean_inc(v_key_3645_);
lean_dec(v_x_3644_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3661_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
uint64_t v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = lean_unbox_uint64(v_key_3645_);
v___x_3652_ = lean_uint64_dec_eq(v___x_3651_, v_a_3642_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3642_, v_b_3643_, v_tail_3647_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 2, v___x_3653_);
v___x_3655_ = v___x_3649_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_key_3645_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_value_3646_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
lean_dec(v_value_3646_);
lean_dec(v_key_3645_);
v___x_3657_ = lean_box_uint64(v_a_3642_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 1, v_b_3643_);
lean_ctor_set(v___x_3649_, 0, v___x_3657_);
v___x_3659_ = v___x_3649_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_b_3643_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_tail_3647_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3662_, lean_object* v_b_3663_, lean_object* v_x_3664_){
_start:
{
uint64_t v_a_boxed_3665_; lean_object* v_res_3666_; 
v_a_boxed_3665_ = lean_unbox_uint64(v_a_3662_);
lean_dec_ref(v_a_3662_);
v_res_3666_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3665_, v_b_3663_, v_x_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3667_, lean_object* v_x_3668_){
_start:
{
if (lean_obj_tag(v_x_3668_) == 0)
{
uint8_t v___x_3669_; 
v___x_3669_ = 0;
return v___x_3669_;
}
else
{
lean_object* v_key_3670_; lean_object* v_tail_3671_; uint64_t v___x_3672_; uint8_t v___x_3673_; 
v_key_3670_ = lean_ctor_get(v_x_3668_, 0);
v_tail_3671_ = lean_ctor_get(v_x_3668_, 2);
v___x_3672_ = lean_unbox_uint64(v_key_3670_);
v___x_3673_ = lean_uint64_dec_eq(v___x_3672_, v_a_3667_);
if (v___x_3673_ == 0)
{
v_x_3668_ = v_tail_3671_;
goto _start;
}
else
{
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3675_, lean_object* v_x_3676_){
_start:
{
uint64_t v_a_boxed_3677_; uint8_t v_res_3678_; lean_object* v_r_3679_; 
v_a_boxed_3677_ = lean_unbox_uint64(v_a_3675_);
lean_dec_ref(v_a_3675_);
v_res_3678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3677_, v_x_3676_);
lean_dec(v_x_3676_);
v_r_3679_ = lean_box(v_res_3678_);
return v_r_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3680_, uint64_t v_a_3681_, lean_object* v_b_3682_){
_start:
{
lean_object* v_size_3683_; lean_object* v_buckets_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3727_; 
v_size_3683_ = lean_ctor_get(v_m_3680_, 0);
v_buckets_3684_ = lean_ctor_get(v_m_3680_, 1);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_m_3680_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3686_ = v_m_3680_;
v_isShared_3687_ = v_isSharedCheck_3727_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_buckets_3684_);
lean_inc(v_size_3683_);
lean_dec(v_m_3680_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3727_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; uint64_t v___x_3689_; uint64_t v___x_3690_; uint64_t v_fold_3691_; uint64_t v___x_3692_; uint64_t v___x_3693_; uint64_t v___x_3694_; size_t v___x_3695_; size_t v___x_3696_; size_t v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; lean_object* v_bkt_3700_; uint8_t v___x_3701_; 
v___x_3688_ = lean_array_get_size(v_buckets_3684_);
v___x_3689_ = 32ULL;
v___x_3690_ = lean_uint64_shift_right(v_a_3681_, v___x_3689_);
v_fold_3691_ = lean_uint64_xor(v_a_3681_, v___x_3690_);
v___x_3692_ = 16ULL;
v___x_3693_ = lean_uint64_shift_right(v_fold_3691_, v___x_3692_);
v___x_3694_ = lean_uint64_xor(v_fold_3691_, v___x_3693_);
v___x_3695_ = lean_uint64_to_usize(v___x_3694_);
v___x_3696_ = lean_usize_of_nat(v___x_3688_);
v___x_3697_ = ((size_t)1ULL);
v___x_3698_ = lean_usize_sub(v___x_3696_, v___x_3697_);
v___x_3699_ = lean_usize_land(v___x_3695_, v___x_3698_);
v_bkt_3700_ = lean_array_uget_borrowed(v_buckets_3684_, v___x_3699_);
v___x_3701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3681_, v_bkt_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v_size_x27_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_buckets_x27_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3702_ = lean_unsigned_to_nat(1u);
v_size_x27_3703_ = lean_nat_add(v_size_3683_, v___x_3702_);
lean_dec(v_size_3683_);
v___x_3704_ = lean_box_uint64(v_a_3681_);
lean_inc(v_bkt_3700_);
v___x_3705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v_b_3682_);
lean_ctor_set(v___x_3705_, 2, v_bkt_3700_);
v_buckets_x27_3706_ = lean_array_uset(v_buckets_3684_, v___x_3699_, v___x_3705_);
v___x_3707_ = lean_unsigned_to_nat(4u);
v___x_3708_ = lean_nat_mul(v_size_x27_3703_, v___x_3707_);
v___x_3709_ = lean_unsigned_to_nat(3u);
v___x_3710_ = lean_nat_div(v___x_3708_, v___x_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_array_get_size(v_buckets_x27_3706_);
v___x_3712_ = lean_nat_dec_le(v___x_3710_, v___x_3711_);
lean_dec(v___x_3710_);
if (v___x_3712_ == 0)
{
lean_object* v_val_3713_; lean_object* v___x_3715_; 
v_val_3713_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3706_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v_val_3713_);
lean_ctor_set(v___x_3686_, 0, v_size_x27_3703_);
v___x_3715_ = v___x_3686_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_size_x27_3703_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_val_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
else
{
lean_object* v___x_3718_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v_buckets_x27_3706_);
lean_ctor_set(v___x_3686_, 0, v_size_x27_3703_);
v___x_3718_ = v___x_3686_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_size_x27_3703_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_buckets_x27_3706_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
else
{
lean_object* v___x_3720_; lean_object* v_buckets_x27_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3725_; 
lean_inc(v_bkt_3700_);
v___x_3720_ = lean_box(0);
v_buckets_x27_3721_ = lean_array_uset(v_buckets_3684_, v___x_3699_, v___x_3720_);
v___x_3722_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3681_, v_b_3682_, v_bkt_3700_);
v___x_3723_ = lean_array_uset(v_buckets_x27_3721_, v___x_3699_, v___x_3722_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___x_3723_);
v___x_3725_ = v___x_3686_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_size_3683_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3728_, lean_object* v_a_3729_, lean_object* v_b_3730_){
_start:
{
uint64_t v_a_boxed_3731_; lean_object* v_res_3732_; 
v_a_boxed_3731_ = lean_unbox_uint64(v_a_3729_);
lean_dec_ref(v_a_3729_);
v_res_3732_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3728_, v_a_boxed_3731_, v_b_3730_);
return v_res_3732_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3733_ = lean_box(0);
v___x_3734_ = lean_unsigned_to_nat(16u);
v___x_3735_ = lean_mk_array(v___x_3734_, v___x_3733_);
return v___x_3735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v_found_3738_; 
v___x_3736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3737_ = lean_unsigned_to_nat(0u);
v_found_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3738_, 0, v___x_3737_);
lean_ctor_set(v_found_3738_, 1, v___x_3736_);
return v_found_3738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_found_3739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3740_ = lean_box(0);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set(v___x_3741_, 1, v_found_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3742_, lean_object* v_numDigits_3743_, lean_object* v_es_3744_, lean_object* v_as_3745_, size_t v_sz_3746_, size_t v_i_3747_, lean_object* v_b_3748_){
_start:
{
lean_object* v_a_3750_; uint8_t v___x_3754_; 
v___x_3754_ = lean_usize_dec_lt(v_i_3747_, v_sz_3746_);
if (v___x_3754_ == 0)
{
return v_b_3748_;
}
else
{
lean_object* v_snd_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3789_; 
v_snd_3755_ = lean_ctor_get(v_b_3748_, 1);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_b_3748_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; 
v_unused_3790_ = lean_ctor_get(v_b_3748_, 0);
lean_dec(v_unused_3790_);
v___x_3757_ = v_b_3748_;
v_isShared_3758_ = v_isSharedCheck_3789_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_snd_3755_);
lean_dec(v_b_3748_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3789_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v_a_3759_; uint64_t v_anchor_3760_; lean_object* v___x_3761_; uint64_t v___x_3762_; uint64_t v___x_3763_; lean_object* v___x_3764_; 
v_a_3759_ = lean_array_uget_borrowed(v_as_3745_, v_i_3747_);
v_anchor_3760_ = lean_ctor_get_uint64(v_a_3759_, sizeof(void*)*3);
v___x_3761_ = lean_box(0);
v___x_3762_ = lean_uint64_of_nat(v_shift_3742_);
v___x_3763_ = lean_uint64_shift_right(v_anchor_3760_, v___x_3762_);
v___x_3764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3755_, v___x_3763_);
if (lean_obj_tag(v___x_3764_) == 1)
{
lean_object* v_val_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3783_; 
v_val_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3783_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_val_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3783_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
uint64_t v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = lean_unbox_uint64(v_val_3765_);
lean_dec(v_val_3765_);
v___x_3770_ = lean_uint64_dec_eq(v___x_3769_, v_anchor_3760_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_nat_add(v_numDigits_3743_, v___x_3771_);
v___x_3773_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3744_, v___x_3772_);
lean_dec(v___x_3772_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3773_);
v___x_3775_ = v___x_3767_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3775_);
v___x_3777_ = v___x_3757_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_snd_3755_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
else
{
lean_object* v___x_3781_; 
lean_del_object(v___x_3767_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3761_);
v___x_3781_ = v___x_3757_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_snd_3755_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
v_a_3750_ = v___x_3781_;
goto v___jp_3749_;
}
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3787_; 
lean_dec(v___x_3764_);
v___x_3784_ = lean_box_uint64(v_anchor_3760_);
v___x_3785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3755_, v___x_3763_, v___x_3784_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 1, v___x_3785_);
lean_ctor_set(v___x_3757_, 0, v___x_3761_);
v___x_3787_ = v___x_3757_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
v_a_3750_ = v___x_3787_;
goto v___jp_3749_;
}
}
}
}
v___jp_3749_:
{
size_t v___x_3751_; size_t v___x_3752_; 
v___x_3751_ = ((size_t)1ULL);
v___x_3752_ = lean_usize_add(v_i_3747_, v___x_3751_);
v_i_3747_ = v___x_3752_;
v_b_3748_ = v_a_3750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3791_, lean_object* v_numDigits_3792_){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3793_ = lean_unsigned_to_nat(4u);
v___x_3794_ = lean_nat_mul(v___x_3793_, v_numDigits_3792_);
v___x_3795_ = lean_unsigned_to_nat(64u);
v___x_3796_ = lean_nat_dec_lt(v___x_3794_, v___x_3795_);
if (v___x_3796_ == 0)
{
lean_dec(v___x_3794_);
lean_inc(v_numDigits_3792_);
return v_numDigits_3792_;
}
else
{
lean_object* v_shift_3797_; lean_object* v___x_3798_; size_t v_sz_3799_; size_t v___x_3800_; lean_object* v___x_3801_; lean_object* v_fst_3802_; 
v_shift_3797_ = lean_nat_sub(v___x_3795_, v___x_3794_);
lean_dec(v___x_3794_);
v___x_3798_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3799_ = lean_array_size(v_es_3791_);
v___x_3800_ = ((size_t)0ULL);
v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3797_, v_numDigits_3792_, v_es_3791_, v_es_3791_, v_sz_3799_, v___x_3800_, v___x_3798_);
lean_dec(v_shift_3797_);
v_fst_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_fst_3802_);
lean_dec_ref(v___x_3801_);
if (lean_obj_tag(v_fst_3802_) == 0)
{
lean_inc(v_numDigits_3792_);
return v_numDigits_3792_;
}
else
{
lean_object* v_val_3803_; 
v_val_3803_ = lean_ctor_get(v_fst_3802_, 0);
lean_inc(v_val_3803_);
lean_dec_ref_known(v_fst_3802_, 1);
return v_val_3803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3804_, lean_object* v_numDigits_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3804_, v_numDigits_3805_);
lean_dec(v_numDigits_3805_);
lean_dec_ref(v_es_3804_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3807_, lean_object* v_numDigits_3808_, lean_object* v_es_3809_, lean_object* v_as_3810_, lean_object* v_sz_3811_, lean_object* v_i_3812_, lean_object* v_b_3813_){
_start:
{
size_t v_sz_boxed_3814_; size_t v_i_boxed_3815_; lean_object* v_res_3816_; 
v_sz_boxed_3814_ = lean_unbox_usize(v_sz_3811_);
lean_dec(v_sz_3811_);
v_i_boxed_3815_ = lean_unbox_usize(v_i_3812_);
lean_dec(v_i_3812_);
v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3807_, v_numDigits_3808_, v_es_3809_, v_as_3810_, v_sz_boxed_3814_, v_i_boxed_3815_, v_b_3813_);
lean_dec_ref(v_as_3810_);
lean_dec_ref(v_es_3809_);
lean_dec(v_numDigits_3808_);
lean_dec(v_shift_3807_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3817_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = lean_unsigned_to_nat(4u);
v___x_3819_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3817_, v___x_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3820_);
lean_dec_ref(v_es_3820_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3822_, lean_object* v_as_3823_, size_t v_i_3824_, size_t v_stop_3825_, lean_object* v_b_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_a_3839_; uint8_t v___x_3843_; 
v___x_3843_ = lean_usize_dec_eq(v_i_3824_, v_stop_3825_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; lean_object* v_e_3845_; lean_object* v___x_3846_; 
v___x_3844_ = lean_array_uget_borrowed(v_as_3823_, v_i_3824_);
v_e_3845_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3844_);
v___x_3846_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3844_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3848_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
lean_inc(v___x_3844_);
v___x_3848_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3844_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
if (lean_obj_tag(v_a_3849_) == 2)
{
lean_object* v_numCases_3850_; uint8_t v_isRec_3851_; lean_object* v___x_3852_; 
v_numCases_3850_ = lean_ctor_get(v_a_3849_, 0);
lean_inc(v_numCases_3850_);
v_isRec_3851_ = lean_ctor_get_uint8(v_a_3849_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3849_, 1);
lean_inc_ref(v_filter_3822_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc(v___y_3827_);
lean_inc_ref(v_e_3845_);
v___x_3852_ = lean_apply_12(v_filter_3822_, v_e_3845_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, lean_box(0));
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; uint8_t v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = lean_unbox(v_a_3853_);
lean_dec(v_a_3853_);
if (v___x_3854_ == 0)
{
lean_dec(v_numCases_3850_);
lean_dec(v_a_3847_);
lean_dec_ref(v_e_3845_);
v_a_3839_ = v_b_3826_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3855_; uint64_t v___x_3856_; lean_object* v___x_3857_; 
lean_inc(v___x_3844_);
v___x_3855_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3855_, 0, v___x_3844_);
lean_ctor_set(v___x_3855_, 1, v_numCases_3850_);
lean_ctor_set(v___x_3855_, 2, v_e_3845_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*3 + 8, v_isRec_3851_);
v___x_3856_ = lean_unbox_uint64(v_a_3847_);
lean_dec(v_a_3847_);
lean_ctor_set_uint64(v___x_3855_, sizeof(void*)*3, v___x_3856_);
v___x_3857_ = lean_array_push(v_b_3826_, v___x_3855_);
v_a_3839_ = v___x_3857_;
goto v___jp_3838_;
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v_numCases_3850_);
lean_dec(v_a_3847_);
lean_dec_ref(v_e_3845_);
lean_dec_ref(v_b_3826_);
lean_dec_ref(v_filter_3822_);
v_a_3858_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3852_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3852_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec_ref(v_e_3845_);
v_a_3839_ = v_b_3826_;
goto v___jp_3838_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_a_3847_);
lean_dec_ref(v_e_3845_);
lean_dec_ref(v_b_3826_);
lean_dec_ref(v_filter_3822_);
v_a_3866_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3848_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3848_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_e_3845_);
lean_dec_ref(v_b_3826_);
lean_dec_ref(v_filter_3822_);
v_a_3874_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3846_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3846_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v___x_3882_; 
lean_dec_ref(v_filter_3822_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v_b_3826_);
return v___x_3882_;
}
v___jp_3838_:
{
size_t v___x_3840_; size_t v___x_3841_; 
v___x_3840_ = ((size_t)1ULL);
v___x_3841_ = lean_usize_add(v_i_3824_, v___x_3840_);
v_i_3824_ = v___x_3841_;
v_b_3826_ = v_a_3839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3883_, lean_object* v_as_3884_, lean_object* v_i_3885_, lean_object* v_stop_3886_, lean_object* v_b_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
size_t v_i_boxed_3899_; size_t v_stop_boxed_3900_; lean_object* v_res_3901_; 
v_i_boxed_3899_ = lean_unbox_usize(v_i_3885_);
lean_dec(v_i_3885_);
v_stop_boxed_3900_ = lean_unbox_usize(v_stop_3886_);
lean_dec(v_stop_3886_);
v_res_3901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3883_, v_as_3884_, v_i_boxed_3899_, v_stop_boxed_3900_, v_b_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v_as_3884_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3904_, lean_object* v_as_3905_, lean_object* v_start_3906_, lean_object* v_stop_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3919_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3920_ = lean_nat_dec_lt(v_start_3906_, v_stop_3907_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
lean_dec_ref(v_filter_3904_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
return v___x_3921_;
}
else
{
lean_object* v___x_3922_; uint8_t v___x_3923_; 
v___x_3922_ = lean_array_get_size(v_as_3905_);
v___x_3923_ = lean_nat_dec_le(v_stop_3907_, v___x_3922_);
if (v___x_3923_ == 0)
{
uint8_t v___x_3924_; 
v___x_3924_ = lean_nat_dec_lt(v_start_3906_, v___x_3922_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; 
lean_dec_ref(v_filter_3904_);
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3919_);
return v___x_3925_;
}
else
{
size_t v___x_3926_; size_t v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_usize_of_nat(v_start_3906_);
v___x_3927_ = lean_usize_of_nat(v___x_3922_);
v___x_3928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3904_, v_as_3905_, v___x_3926_, v___x_3927_, v___x_3919_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
return v___x_3928_;
}
}
else
{
size_t v___x_3929_; size_t v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_usize_of_nat(v_start_3906_);
v___x_3930_ = lean_usize_of_nat(v_stop_3907_);
v___x_3931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3904_, v_as_3905_, v___x_3929_, v___x_3930_, v___x_3919_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
return v___x_3931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3932_, lean_object* v_as_3933_, lean_object* v_start_3934_, lean_object* v_stop_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3932_, v_as_3933_, v_start_3934_, v_stop_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v_stop_3935_);
lean_dec(v_start_3934_);
lean_dec_ref(v_as_3933_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3948_, lean_object* v_candidates_x3f_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_candidates_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; 
if (lean_obj_tag(v_candidates_x3f_3949_) == 0)
{
lean_object* v___x_3995_; lean_object* v_toGoalState_3996_; lean_object* v_split_3997_; lean_object* v_candidates_3998_; 
v___x_3995_ = lean_st_ref_get(v_a_3950_);
v_toGoalState_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_ref(v_toGoalState_3996_);
lean_dec(v___x_3995_);
v_split_3997_ = lean_ctor_get(v_toGoalState_3996_, 14);
lean_inc_ref(v_split_3997_);
lean_dec_ref(v_toGoalState_3996_);
v_candidates_3998_ = lean_ctor_get(v_split_3997_, 1);
lean_inc(v_candidates_3998_);
lean_dec_ref(v_split_3997_);
v_candidates_3962_ = v_candidates_3998_;
v___y_3963_ = v_a_3950_;
v___y_3964_ = v_a_3951_;
v___y_3965_ = v_a_3952_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
v___y_3969_ = v_a_3956_;
v___y_3970_ = v_a_3957_;
v___y_3971_ = v_a_3958_;
v___y_3972_ = v_a_3959_;
goto v___jp_3961_;
}
else
{
lean_object* v_val_3999_; 
v_val_3999_ = lean_ctor_get(v_candidates_x3f_3949_, 0);
lean_inc(v_val_3999_);
lean_dec_ref_known(v_candidates_x3f_3949_, 1);
v_candidates_3962_ = v_val_3999_;
v___y_3963_ = v_a_3950_;
v___y_3964_ = v_a_3951_;
v___y_3965_ = v_a_3952_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
v___y_3969_ = v_a_3956_;
v___y_3970_ = v_a_3957_;
v___y_3971_ = v_a_3958_;
v___y_3972_ = v_a_3959_;
goto v___jp_3961_;
}
v___jp_3961_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3973_ = lean_array_mk(v_candidates_3962_);
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = lean_array_get_size(v___x_3973_);
v___x_3976_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3948_, v___x_3973_, v___x_3974_, v___x_3975_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec_ref(v___x_3973_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3986_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3986_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3986_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3984_; 
v___x_3981_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3977_);
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v_a_3977_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_3982_);
v___x_3984_ = v___x_3979_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
v_a_3987_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3976_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3976_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4000_, lean_object* v_candidates_x3f_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4000_, v_candidates_x3f_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec(v_a_4002_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4014_, lean_object* v_m_4015_, uint64_t v_a_4016_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4015_, v_a_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4018_, lean_object* v_m_4019_, lean_object* v_a_4020_){
_start:
{
uint64_t v_a_boxed_4021_; lean_object* v_res_4022_; 
v_a_boxed_4021_ = lean_unbox_uint64(v_a_4020_);
lean_dec_ref(v_a_4020_);
v_res_4022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4018_, v_m_4019_, v_a_boxed_4021_);
lean_dec_ref(v_m_4019_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4023_, lean_object* v_m_4024_, uint64_t v_a_4025_, lean_object* v_b_4026_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4024_, v_a_4025_, v_b_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4028_, lean_object* v_m_4029_, lean_object* v_a_4030_, lean_object* v_b_4031_){
_start:
{
uint64_t v_a_boxed_4032_; lean_object* v_res_4033_; 
v_a_boxed_4032_ = lean_unbox_uint64(v_a_4030_);
lean_dec_ref(v_a_4030_);
v_res_4033_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4028_, v_m_4029_, v_a_boxed_4032_, v_b_4031_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4034_, uint64_t v_a_4035_, lean_object* v_x_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4035_, v_x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4038_, lean_object* v_a_4039_, lean_object* v_x_4040_){
_start:
{
uint64_t v_a_boxed_4041_; lean_object* v_res_4042_; 
v_a_boxed_4041_ = lean_unbox_uint64(v_a_4039_);
lean_dec_ref(v_a_4039_);
v_res_4042_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4038_, v_a_boxed_4041_, v_x_4040_);
lean_dec(v_x_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4043_, uint64_t v_a_4044_, lean_object* v_x_4045_){
_start:
{
uint8_t v___x_4046_; 
v___x_4046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4044_, v_x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4047_, lean_object* v_a_4048_, lean_object* v_x_4049_){
_start:
{
uint64_t v_a_boxed_4050_; uint8_t v_res_4051_; lean_object* v_r_4052_; 
v_a_boxed_4050_ = lean_unbox_uint64(v_a_4048_);
lean_dec_ref(v_a_4048_);
v_res_4051_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4047_, v_a_boxed_4050_, v_x_4049_);
lean_dec(v_x_4049_);
v_r_4052_ = lean_box(v_res_4051_);
return v_r_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4053_, lean_object* v_data_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4056_, uint64_t v_a_4057_, lean_object* v_b_4058_, lean_object* v_x_4059_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4057_, v_b_4058_, v_x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4061_, lean_object* v_a_4062_, lean_object* v_b_4063_, lean_object* v_x_4064_){
_start:
{
uint64_t v_a_boxed_4065_; lean_object* v_res_4066_; 
v_a_boxed_4065_ = lean_unbox_uint64(v_a_4062_);
lean_dec_ref(v_a_4062_);
v_res_4066_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4061_, v_a_boxed_4065_, v_b_4063_, v_x_4064_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4067_, lean_object* v_i_4068_, lean_object* v_source_4069_, lean_object* v_target_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4068_, v_source_4069_, v_target_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4072_, lean_object* v_x_4073_, lean_object* v_x_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4073_, v_x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = 1;
v___x_4089_ = lean_box(v___x_4088_);
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v_x_4091_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4104_, uint64_t v_a_4105_, lean_object* v_c_4106_, lean_object* v_numDigits_4107_, lean_object* v_as_4108_, size_t v_sz_4109_, size_t v_i_4110_, lean_object* v_b_4111_){
_start:
{
lean_object* v_a_4114_; uint8_t v___x_4118_; 
v___x_4118_ = lean_usize_dec_lt(v_i_4110_, v_sz_4109_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; 
lean_dec(v_numDigits_4107_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_b_4111_);
return v___x_4119_;
}
else
{
lean_object* v_snd_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4146_; 
v_snd_4120_ = lean_ctor_get(v_b_4111_, 1);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_b_4111_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_b_4111_, 0);
lean_dec(v_unused_4147_);
v___x_4122_ = v_b_4111_;
v_isShared_4123_ = v_isSharedCheck_4146_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_snd_4120_);
lean_dec(v_b_4111_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4146_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v_a_4124_; lean_object* v_c_4125_; uint64_t v_anchor_4126_; lean_object* v___x_4127_; uint64_t v___x_4128_; uint64_t v___x_4129_; uint8_t v___x_4130_; 
v_a_4124_ = lean_array_uget_borrowed(v_as_4108_, v_i_4110_);
v_c_4125_ = lean_ctor_get(v_a_4124_, 0);
v_anchor_4126_ = lean_ctor_get_uint64(v_a_4124_, sizeof(void*)*3);
v___x_4127_ = lean_box(0);
v___x_4128_ = lean_uint64_shift_right(v_anchor_4126_, v___x_4104_);
v___x_4129_ = lean_uint64_shift_right(v_a_4105_, v___x_4104_);
v___x_4130_ = lean_uint64_dec_eq(v___x_4128_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4132_; 
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v___x_4127_);
v___x_4132_ = v___x_4122_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_snd_4120_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
v_a_4114_ = v___x_4132_;
goto v___jp_4113_;
}
}
else
{
uint8_t v___x_4134_; 
v___x_4134_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4125_, v_c_4106_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4135_ = lean_unsigned_to_nat(1u);
v___x_4136_ = lean_nat_add(v_snd_4120_, v___x_4135_);
lean_dec(v_snd_4120_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 1, v___x_4136_);
lean_ctor_set(v___x_4122_, 0, v___x_4127_);
v___x_4138_ = v___x_4122_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
v_a_4114_ = v___x_4138_;
goto v___jp_4113_;
}
}
else
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
lean_inc(v_snd_4120_);
v___x_4140_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4140_, 0, v_numDigits_4107_);
lean_ctor_set(v___x_4140_, 1, v_snd_4120_);
lean_ctor_set_uint64(v___x_4140_, sizeof(void*)*2, v_a_4105_);
v___x_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v___x_4141_);
v___x_4143_ = v___x_4122_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_snd_4120_);
v___x_4143_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4144_; 
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
}
}
}
}
v___jp_4113_:
{
size_t v___x_4115_; size_t v___x_4116_; 
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_add(v_i_4110_, v___x_4115_);
v_i_4110_ = v___x_4116_;
v_b_4111_ = v_a_4114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4148_, lean_object* v_a_4149_, lean_object* v_c_4150_, lean_object* v_numDigits_4151_, lean_object* v_as_4152_, lean_object* v_sz_4153_, lean_object* v_i_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_){
_start:
{
uint64_t v___x_7681__boxed_4157_; uint64_t v_a_7682__boxed_4158_; size_t v_sz_boxed_4159_; size_t v_i_boxed_4160_; lean_object* v_res_4161_; 
v___x_7681__boxed_4157_ = lean_unbox_uint64(v___x_4148_);
lean_dec_ref(v___x_4148_);
v_a_7682__boxed_4158_ = lean_unbox_uint64(v_a_4149_);
lean_dec_ref(v_a_4149_);
v_sz_boxed_4159_ = lean_unbox_usize(v_sz_4153_);
lean_dec(v_sz_4153_);
v_i_boxed_4160_ = lean_unbox_usize(v_i_4154_);
lean_dec(v_i_4154_);
v_res_4161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7681__boxed_4157_, v_a_7682__boxed_4158_, v_c_4150_, v_numDigits_4151_, v_as_4152_, v_sz_boxed_4159_, v_i_boxed_4160_, v_b_4155_);
lean_dec_ref(v_as_4152_);
lean_dec_ref(v_c_4150_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4166_, lean_object* v_candidates_x3f_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v___f_4179_; lean_object* v___x_4180_; 
v___f_4179_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4180_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4179_, v_candidates_x3f_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v_candidates_4182_; lean_object* v_numDigits_4183_; lean_object* v___x_4184_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v_candidates_4182_ = lean_ctor_get(v_a_4181_, 0);
lean_inc_ref(v_candidates_4182_);
v_numDigits_4183_ = lean_ctor_get(v_a_4181_, 1);
lean_inc(v_numDigits_4183_);
lean_dec(v_a_4181_);
v___x_4184_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4166_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint64_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; size_t v_sz_4193_; size_t v___x_4194_; uint64_t v___x_4195_; lean_object* v___x_4196_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4184_, 1);
v___x_4186_ = lean_unsigned_to_nat(64u);
v___x_4187_ = lean_unsigned_to_nat(4u);
v___x_4188_ = lean_nat_mul(v___x_4187_, v_numDigits_4183_);
v___x_4189_ = lean_nat_sub(v___x_4186_, v___x_4188_);
lean_dec(v___x_4188_);
v___x_4190_ = lean_uint64_of_nat(v___x_4189_);
lean_dec(v___x_4189_);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4193_ = lean_array_size(v_candidates_4182_);
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = lean_unbox_uint64(v_a_4185_);
lean_inc(v_numDigits_4183_);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4190_, v___x_4195_, v_c_4166_, v_numDigits_4183_, v_candidates_4182_, v_sz_4193_, v___x_4194_, v___x_4192_);
lean_dec_ref(v_candidates_4182_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4211_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4211_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4211_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v_fst_4201_; 
v_fst_4201_ = lean_ctor_get(v_a_4197_, 0);
lean_inc(v_fst_4201_);
lean_dec(v_a_4197_);
if (lean_obj_tag(v_fst_4201_) == 0)
{
lean_object* v___x_4202_; uint64_t v___x_4203_; lean_object* v___x_4205_; 
v___x_4202_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4202_, 0, v_numDigits_4183_);
lean_ctor_set(v___x_4202_, 1, v___x_4191_);
v___x_4203_ = lean_unbox_uint64(v_a_4185_);
lean_dec(v_a_4185_);
lean_ctor_set_uint64(v___x_4202_, sizeof(void*)*2, v___x_4203_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4202_);
v___x_4205_ = v___x_4199_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4202_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
else
{
lean_object* v_val_4207_; lean_object* v___x_4209_; 
lean_dec(v_a_4185_);
lean_dec(v_numDigits_4183_);
v_val_4207_ = lean_ctor_get(v_fst_4201_, 0);
lean_inc(v_val_4207_);
lean_dec_ref_known(v_fst_4201_, 1);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_val_4207_);
v___x_4209_ = v___x_4199_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_val_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec(v_a_4185_);
lean_dec(v_numDigits_4183_);
v_a_4212_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4196_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4196_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_numDigits_4183_);
lean_dec_ref(v_candidates_4182_);
v_a_4220_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4184_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4184_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4180_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4180_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4236_, lean_object* v_candidates_x3f_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4236_, v_candidates_x3f_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4240_);
lean_dec(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_c_4236_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4250_, uint64_t v_a_4251_, lean_object* v_c_4252_, lean_object* v_numDigits_4253_, lean_object* v_as_4254_, size_t v_sz_4255_, size_t v_i_4256_, lean_object* v_b_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4250_, v_a_4251_, v_c_4252_, v_numDigits_4253_, v_as_4254_, v_sz_4255_, v_i_4256_, v_b_4257_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4270_ = _args[0];
lean_object* v_a_4271_ = _args[1];
lean_object* v_c_4272_ = _args[2];
lean_object* v_numDigits_4273_ = _args[3];
lean_object* v_as_4274_ = _args[4];
lean_object* v_sz_4275_ = _args[5];
lean_object* v_i_4276_ = _args[6];
lean_object* v_b_4277_ = _args[7];
lean_object* v___y_4278_ = _args[8];
lean_object* v___y_4279_ = _args[9];
lean_object* v___y_4280_ = _args[10];
lean_object* v___y_4281_ = _args[11];
lean_object* v___y_4282_ = _args[12];
lean_object* v___y_4283_ = _args[13];
lean_object* v___y_4284_ = _args[14];
lean_object* v___y_4285_ = _args[15];
lean_object* v___y_4286_ = _args[16];
lean_object* v___y_4287_ = _args[17];
lean_object* v___y_4288_ = _args[18];
_start:
{
uint64_t v___x_7880__boxed_4289_; uint64_t v_a_7881__boxed_4290_; size_t v_sz_boxed_4291_; size_t v_i_boxed_4292_; lean_object* v_res_4293_; 
v___x_7880__boxed_4289_ = lean_unbox_uint64(v___x_4270_);
lean_dec_ref(v___x_4270_);
v_a_7881__boxed_4290_ = lean_unbox_uint64(v_a_4271_);
lean_dec_ref(v_a_4271_);
v_sz_boxed_4291_ = lean_unbox_usize(v_sz_4275_);
lean_dec(v_sz_4275_);
v_i_boxed_4292_ = lean_unbox_usize(v_i_4276_);
lean_dec(v_i_4276_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7880__boxed_4289_, v_a_7881__boxed_4290_, v_c_4272_, v_numDigits_4273_, v_as_4274_, v_sz_boxed_4291_, v_i_boxed_4292_, v_b_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v_as_4274_);
lean_dec_ref(v_c_4272_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_numDigits_4321_; uint64_t v_anchor_4322_; lean_object* v_ordinal_4323_; lean_object* v___x_4324_; 
v_numDigits_4321_ = lean_ctor_get(v_info_4318_, 0);
v_anchor_4322_ = lean_ctor_get_uint64(v_info_4318_, sizeof(void*)*2);
v_ordinal_4323_ = lean_ctor_get(v_info_4318_, 1);
v___x_4324_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4321_, v_anchor_4322_, v_a_4319_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4361_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4361_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4361_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; uint8_t v___x_4330_; 
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = lean_nat_dec_eq(v_ordinal_4323_, v___x_4329_);
if (v___x_4330_ == 0)
{
lean_object* v_ref_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4347_; 
v_ref_4331_ = lean_ctor_get(v_a_4319_, 2);
v___x_4332_ = l_Lean_SourceInfo_fromRef(v_ref_4331_, v___x_4330_);
v___x_4333_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4334_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4332_, 3);
v___x_4335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4332_);
lean_ctor_set(v___x_4335_, 1, v___x_4333_);
v___x_4336_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4337_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4332_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = lean_unsigned_to_nat(1u);
v___x_4340_ = lean_nat_add(v_ordinal_4323_, v___x_4339_);
v___x_4341_ = l_Nat_reprFast(v___x_4340_);
v___x_4342_ = lean_box(2);
v___x_4343_ = l_Lean_Syntax_mkNumLit(v___x_4341_, v___x_4342_);
v___x_4344_ = l_Lean_Syntax_node3(v___x_4332_, v___x_4336_, v_a_4325_, v___x_4338_, v___x_4343_);
v___x_4345_ = l_Lean_Syntax_node2(v___x_4332_, v___x_4334_, v___x_4335_, v___x_4344_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4345_);
v___x_4347_ = v___x_4327_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
else
{
lean_object* v_ref_4349_; uint8_t v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4359_; 
v_ref_4349_ = lean_ctor_get(v_a_4319_, 2);
v___x_4350_ = 0;
v___x_4351_ = l_Lean_SourceInfo_fromRef(v_ref_4349_, v___x_4350_);
v___x_4352_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4353_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4351_, 2);
v___x_4354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4351_);
lean_ctor_set(v___x_4354_, 1, v___x_4352_);
v___x_4355_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4356_ = l_Lean_Syntax_node1(v___x_4351_, v___x_4355_, v_a_4325_);
v___x_4357_ = l_Lean_Syntax_node2(v___x_4351_, v___x_4353_, v___x_4354_, v___x_4356_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4357_);
v___x_4359_ = v___x_4327_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
return v___x_4324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4362_, v_a_4363_);
lean_dec_ref(v_a_4363_);
lean_dec_ref(v_info_4362_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4366_, v_a_4367_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4371_, v_a_4372_, v_a_4373_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec_ref(v_info_4371_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v_p_4407_; lean_object* v___x_4410_; 
lean_inc_ref(v_proof_4388_);
v___x_4410_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4388_, v_a_4390_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4437_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4437_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4437_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; uint8_t v___x_4416_; 
v___x_4415_ = l_Lean_Expr_cleanupAnnotations(v_a_4411_);
v___x_4416_ = l_Lean_Expr_isApp(v___x_4415_);
if (v___x_4416_ == 0)
{
lean_dec_ref(v___x_4415_);
lean_del_object(v___x_4413_);
v___y_4395_ = v_a_4389_;
v___y_4396_ = v_a_4390_;
v___y_4397_ = v_a_4391_;
v___y_4398_ = v_a_4392_;
goto v___jp_4394_;
}
else
{
lean_object* v_arg_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; 
v_arg_4417_ = lean_ctor_get(v___x_4415_, 1);
lean_inc_ref(v_arg_4417_);
v___x_4418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4415_);
v___x_4419_ = l_Lean_Expr_isApp(v___x_4418_);
if (v___x_4419_ == 0)
{
lean_dec_ref(v___x_4418_);
lean_dec_ref(v_arg_4417_);
lean_del_object(v___x_4413_);
v___y_4395_ = v_a_4389_;
v___y_4396_ = v_a_4390_;
v___y_4397_ = v_a_4391_;
v___y_4398_ = v_a_4392_;
goto v___jp_4394_;
}
else
{
lean_object* v_arg_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v_arg_4420_ = lean_ctor_get(v___x_4418_, 1);
lean_inc_ref(v_arg_4420_);
v___x_4421_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4418_);
v___x_4422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4423_ = l_Lean_Expr_isConstOf(v___x_4421_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; uint8_t v___x_4425_; 
lean_dec_ref(v_arg_4420_);
lean_del_object(v___x_4413_);
v___x_4424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4425_ = l_Lean_Expr_isConstOf(v___x_4421_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; uint8_t v___x_4427_; 
v___x_4426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4427_ = l_Lean_Expr_isConstOf(v___x_4421_, v___x_4426_);
lean_dec_ref(v___x_4421_);
if (v___x_4427_ == 0)
{
lean_dec_ref(v_arg_4417_);
v___y_4395_ = v_a_4389_;
v___y_4396_ = v_a_4390_;
v___y_4397_ = v_a_4391_;
v___y_4398_ = v_a_4392_;
goto v___jp_4394_;
}
else
{
lean_dec_ref(v_proof_4388_);
v_p_4407_ = v_arg_4417_;
goto v___jp_4406_;
}
}
else
{
lean_dec_ref(v___x_4421_);
lean_dec_ref(v_proof_4388_);
v_p_4407_ = v_arg_4417_;
goto v___jp_4406_;
}
}
else
{
uint8_t v___x_4428_; 
lean_dec_ref(v___x_4421_);
lean_dec_ref(v_proof_4388_);
v___x_4428_ = l_Lean_Expr_isFalse(v_arg_4420_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_dec_ref(v_arg_4417_);
v___x_4429_ = lean_box(0);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4429_);
v___x_4431_ = v___x_4413_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
else
{
lean_object* v___x_4433_; lean_object* v___x_4435_; 
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v_arg_4417_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4433_);
v___x_4435_ = v___x_4413_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec_ref(v_proof_4388_);
v_a_4438_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4410_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4410_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
v___jp_4394_:
{
if (lean_obj_tag(v_proof_4388_) == 6)
{
lean_object* v_body_4399_; uint8_t v___x_4400_; 
v_body_4399_ = lean_ctor_get(v_proof_4388_, 2);
lean_inc_ref(v_body_4399_);
lean_dec_ref_known(v_proof_4388_, 3);
v___x_4400_ = l_Lean_Expr_hasLooseBVars(v_body_4399_);
if (v___x_4400_ == 0)
{
v_proof_4388_ = v_body_4399_;
v_a_4389_ = v___y_4395_;
v_a_4390_ = v___y_4396_;
v_a_4391_ = v___y_4397_;
v_a_4392_ = v___y_4398_;
goto _start;
}
else
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
lean_dec_ref(v_body_4399_);
v___x_4402_ = lean_box(0);
v___x_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4402_);
return v___x_4403_;
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_dec_ref(v_proof_4388_);
v___x_4404_ = lean_box(0);
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
}
v___jp_4406_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4408_, 0, v_p_4407_);
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
return v___x_4409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4453_, lean_object* v___y_4454_){
_start:
{
uint8_t v___x_4456_; 
v___x_4456_ = l_Lean_Expr_hasMVar(v_e_4453_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v_e_4453_);
return v___x_4457_;
}
else
{
lean_object* v___x_4458_; lean_object* v_mctx_4459_; lean_object* v___x_4460_; lean_object* v_fst_4461_; lean_object* v_snd_4462_; lean_object* v___x_4463_; lean_object* v_cache_4464_; lean_object* v_zetaDeltaFVarIds_4465_; lean_object* v_postponed_4466_; lean_object* v_diag_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4476_; 
v___x_4458_ = lean_st_ref_get(v___y_4454_);
v_mctx_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc_ref(v_mctx_4459_);
lean_dec(v___x_4458_);
v___x_4460_ = l_Lean_instantiateMVarsCore(v_mctx_4459_, v_e_4453_);
v_fst_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_fst_4461_);
v_snd_4462_ = lean_ctor_get(v___x_4460_, 1);
lean_inc(v_snd_4462_);
lean_dec_ref(v___x_4460_);
v___x_4463_ = lean_st_ref_take(v___y_4454_);
v_cache_4464_ = lean_ctor_get(v___x_4463_, 1);
v_zetaDeltaFVarIds_4465_ = lean_ctor_get(v___x_4463_, 2);
v_postponed_4466_ = lean_ctor_get(v___x_4463_, 3);
v_diag_4467_ = lean_ctor_get(v___x_4463_, 4);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; 
v_unused_4477_ = lean_ctor_get(v___x_4463_, 0);
lean_dec(v_unused_4477_);
v___x_4469_ = v___x_4463_;
v_isShared_4470_ = v_isSharedCheck_4476_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_diag_4467_);
lean_inc(v_postponed_4466_);
lean_inc(v_zetaDeltaFVarIds_4465_);
lean_inc(v_cache_4464_);
lean_dec(v___x_4463_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4476_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v_snd_4462_);
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_snd_4462_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_cache_4464_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v_zetaDeltaFVarIds_4465_);
lean_ctor_set(v_reuseFailAlloc_4475_, 3, v_postponed_4466_);
lean_ctor_set(v_reuseFailAlloc_4475_, 4, v_diag_4467_);
v___x_4472_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = lean_st_ref_put(v___y_4454_, v___x_4472_);
v___x_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4474_, 0, v_fst_4461_);
return v___x_4474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4478_, v___y_4479_);
lean_dec(v___y_4479_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4482_, v___y_4484_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4496_, lean_object* v_x_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v___x_4503_; 
v___x_4503_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4496_, v_x_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4503_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4503_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_a_4512_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4503_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4503_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4520_, lean_object* v_x_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4520_, v_x_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4528_, lean_object* v_mvarId_4529_, lean_object* v_x_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4529_, v_x_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4537_, lean_object* v_mvarId_4538_, lean_object* v_x_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4537_, v_mvarId_4538_, v_x_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4563_; 
v___x_4552_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4546_, v___y_4548_);
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4555_ = v___x_4552_;
v_isShared_4556_ = v_isSharedCheck_4563_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4563_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
uint8_t v___x_4557_; 
v___x_4557_ = l_Lean_Expr_hasSyntheticSorry(v_a_4553_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4558_; 
lean_del_object(v___x_4555_);
v___x_4558_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4553_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
return v___x_4558_;
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4561_; 
lean_dec(v_a_4553_);
v___x_4559_ = lean_box(0);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v___x_4559_);
v___x_4561_ = v___x_4555_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v___x_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; 
lean_inc(v_mvarId_4571_);
v___x_4577_ = l_Lean_mkMVar(v_mvarId_4571_);
v___f_4578_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4578_, 0, v___x_4577_);
v___x_4579_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4571_, v___f_4578_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
return v_res_4586_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4608_){
_start:
{
if (lean_obj_tag(v_x_4608_) == 0)
{
uint8_t v___x_4609_; 
v___x_4609_ = 1;
return v___x_4609_;
}
else
{
lean_object* v_head_4610_; lean_object* v_tail_4611_; uint8_t v___y_4613_; lean_object* v___x_4615_; uint8_t v___x_4616_; 
v_head_4610_ = lean_ctor_get(v_x_4608_, 0);
lean_inc_n(v_head_4610_, 2);
v_tail_4611_ = lean_ctor_get(v_x_4608_, 1);
lean_inc(v_tail_4611_);
lean_dec_ref_known(v_x_4608_, 2);
v___x_4615_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4616_ = l_Lean_Syntax_isOfKind(v_head_4610_, v___x_4615_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4617_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4610_);
v___x_4618_ = l_Lean_Syntax_isOfKind(v_head_4610_, v___x_4617_);
if (v___x_4618_ == 0)
{
lean_dec(v_head_4610_);
v_x_4608_ = v_tail_4611_;
goto _start;
}
else
{
if (v___x_4616_ == 0)
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; 
v___x_4620_ = lean_unsigned_to_nat(1u);
v___x_4621_ = l_Lean_Syntax_getArg(v_head_4610_, v___x_4620_);
lean_dec(v_head_4610_);
v___x_4622_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4623_ = l_Lean_Syntax_isOfKind(v___x_4621_, v___x_4622_);
if (v___x_4623_ == 0)
{
v_x_4608_ = v_tail_4611_;
goto _start;
}
else
{
v___y_4613_ = v___x_4616_;
goto v___jp_4612_;
}
}
else
{
lean_dec(v_head_4610_);
v___y_4613_ = v___x_4616_;
goto v___jp_4612_;
}
}
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4625_ = lean_unsigned_to_nat(3u);
v___x_4626_ = l_Lean_Syntax_getArg(v_head_4610_, v___x_4625_);
lean_dec(v_head_4610_);
v___x_4627_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4628_ = l_Lean_Syntax_isOfKind(v___x_4626_, v___x_4627_);
if (v___x_4628_ == 0)
{
v_x_4608_ = v_tail_4611_;
goto _start;
}
else
{
uint8_t v___x_4630_; 
lean_dec(v_tail_4611_);
v___x_4630_ = 0;
return v___x_4630_;
}
}
v___jp_4612_:
{
if (v___y_4613_ == 0)
{
lean_dec(v_tail_4611_);
return v___y_4613_;
}
else
{
v_x_4608_ = v_tail_4611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4631_){
_start:
{
uint8_t v_res_4632_; lean_object* v_r_4633_; 
v_res_4632_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4631_);
v_r_4633_ = lean_box(v_res_4632_);
return v_r_4633_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4634_){
_start:
{
uint8_t v___x_4635_; 
v___x_4635_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4634_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4636_){
_start:
{
uint8_t v_res_4637_; lean_object* v_r_4638_; 
v_res_4637_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4636_);
v_r_4638_ = lean_box(v_res_4637_);
return v_r_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4654_, lean_object* v_a_4655_){
_start:
{
if (lean_obj_tag(v_seq_4654_) == 0)
{
lean_object* v_ref_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v_ref_4657_ = lean_ctor_get(v_a_4655_, 2);
v___x_4658_ = 0;
v___x_4659_ = l_Lean_SourceInfo_fromRef(v_ref_4657_, v___x_4658_);
v___x_4660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4659_);
v___x_4662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4659_);
lean_ctor_set(v___x_4662_, 1, v___x_4660_);
v___x_4663_ = l_Lean_Syntax_node1(v___x_4659_, v___x_4661_, v___x_4662_);
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
return v___x_4664_;
}
else
{
lean_object* v_tail_4665_; 
v_tail_4665_ = lean_ctor_get(v_seq_4654_, 1);
if (lean_obj_tag(v_tail_4665_) == 0)
{
lean_object* v_head_4666_; lean_object* v___x_4667_; 
v_head_4666_ = lean_ctor_get(v_seq_4654_, 0);
lean_inc(v_head_4666_);
lean_dec_ref_known(v_seq_4654_, 2);
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v_head_4666_);
return v___x_4667_;
}
else
{
lean_object* v_head_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4690_; 
lean_inc(v_tail_4665_);
v_head_4668_ = lean_ctor_get(v_seq_4654_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_seq_4654_);
if (v_isSharedCheck_4690_ == 0)
{
lean_object* v_unused_4691_; 
v_unused_4691_ = lean_ctor_get(v_seq_4654_, 1);
lean_dec(v_unused_4691_);
v___x_4670_ = v_seq_4654_;
v_isShared_4671_ = v_isSharedCheck_4690_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_head_4668_);
lean_dec(v_seq_4654_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4690_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4689_; 
v___x_4672_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4665_, v_a_4655_);
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4675_ = v___x_4672_;
v_isShared_4676_ = v_isSharedCheck_4689_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4672_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4689_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v_ref_4677_; uint8_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4683_; 
v_ref_4677_ = lean_ctor_get(v_a_4655_, 2);
v___x_4678_ = 0;
v___x_4679_ = l_Lean_SourceInfo_fromRef(v_ref_4677_, v___x_4678_);
v___x_4680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4679_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set_tag(v___x_4670_, 2);
lean_ctor_set(v___x_4670_, 1, v___x_4681_);
lean_ctor_set(v___x_4670_, 0, v___x_4679_);
v___x_4683_ = v___x_4670_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; lean_object* v___x_4686_; 
v___x_4684_ = l_Lean_Syntax_node3(v___x_4679_, v___x_4680_, v_head_4668_, v___x_4683_, v_a_4673_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v___x_4684_);
v___x_4686_ = v___x_4675_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4692_, v_a_4693_);
lean_dec_ref(v_a_4693_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4696_, v_a_4697_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4701_, v_a_4702_, v_a_4703_);
lean_dec(v_a_4703_);
lean_dec_ref(v_a_4702_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4706_, lean_object* v_seq_4707_, lean_object* v_a_4708_){
_start:
{
if (lean_obj_tag(v_seq_4707_) == 0)
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v_cases_4706_);
return v___x_4710_;
}
else
{
lean_object* v___x_4711_; lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4726_; 
v___x_4711_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4707_, v_a_4708_);
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4714_ = v___x_4711_;
v_isShared_4715_ = v_isSharedCheck_4726_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4726_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v_ref_4716_; uint8_t v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
v_ref_4716_ = lean_ctor_get(v_a_4708_, 2);
v___x_4717_ = 0;
v___x_4718_ = l_Lean_SourceInfo_fromRef(v_ref_4716_, v___x_4717_);
v___x_4719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4718_);
v___x_4721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4718_);
lean_ctor_set(v___x_4721_, 1, v___x_4720_);
v___x_4722_ = l_Lean_Syntax_node3(v___x_4718_, v___x_4719_, v_cases_4706_, v___x_4721_, v_a_4712_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 0, v___x_4722_);
v___x_4724_ = v___x_4714_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4727_, lean_object* v_seq_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4727_, v_seq_4728_, v_a_4729_);
lean_dec_ref(v_a_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4732_, lean_object* v_seq_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4732_, v_seq_4733_, v_a_4734_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4738_, lean_object* v_seq_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4738_, v_seq_4739_, v_a_4740_, v_a_4741_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4743_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4744_, lean_object* v_x_4745_){
_start:
{
if (lean_obj_tag(v_x_4744_) == 0)
{
if (lean_obj_tag(v_x_4745_) == 0)
{
uint8_t v___x_4746_; 
v___x_4746_ = 1;
return v___x_4746_;
}
else
{
uint8_t v___x_4747_; 
v___x_4747_ = 0;
return v___x_4747_;
}
}
else
{
if (lean_obj_tag(v_x_4745_) == 0)
{
uint8_t v___x_4748_; 
v___x_4748_ = 0;
return v___x_4748_;
}
else
{
lean_object* v_head_4749_; lean_object* v_tail_4750_; lean_object* v_head_4751_; lean_object* v_tail_4752_; uint8_t v___x_4753_; 
v_head_4749_ = lean_ctor_get(v_x_4744_, 0);
v_tail_4750_ = lean_ctor_get(v_x_4744_, 1);
v_head_4751_ = lean_ctor_get(v_x_4745_, 0);
v_tail_4752_ = lean_ctor_get(v_x_4745_, 1);
v___x_4753_ = l_Lean_Syntax_structEq(v_head_4749_, v_head_4751_);
if (v___x_4753_ == 0)
{
return v___x_4753_;
}
else
{
v_x_4744_ = v_tail_4750_;
v_x_4745_ = v_tail_4752_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4755_, lean_object* v_x_4756_){
_start:
{
uint8_t v_res_4757_; lean_object* v_r_4758_; 
v_res_4757_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4755_, v_x_4756_);
lean_dec(v_x_4756_);
lean_dec(v_x_4755_);
v_r_4758_ = lean_box(v_res_4757_);
return v_r_4758_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4759_, lean_object* v___x_4760_, lean_object* v_as_4761_, size_t v_i_4762_, size_t v_stop_4763_){
_start:
{
uint8_t v___x_4768_; 
v___x_4768_ = lean_usize_dec_eq(v_i_4762_, v_stop_4763_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; uint8_t v___x_4770_; 
v___x_4769_ = lean_array_uget_borrowed(v_as_4761_, v_i_4762_);
v___x_4770_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4769_, v_alt_4759_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; uint8_t v___x_4772_; 
v___x_4771_ = lean_unsigned_to_nat(0u);
v___x_4772_ = lean_nat_dec_lt(v___x_4771_, v___x_4760_);
if (v___x_4772_ == 0)
{
goto v___jp_4764_;
}
else
{
return v___x_4772_;
}
}
else
{
goto v___jp_4764_;
}
}
else
{
uint8_t v___x_4773_; 
v___x_4773_ = 0;
return v___x_4773_;
}
v___jp_4764_:
{
size_t v___x_4765_; size_t v___x_4766_; 
v___x_4765_ = ((size_t)1ULL);
v___x_4766_ = lean_usize_add(v_i_4762_, v___x_4765_);
v_i_4762_ = v___x_4766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4774_, lean_object* v___x_4775_, lean_object* v_as_4776_, lean_object* v_i_4777_, lean_object* v_stop_4778_){
_start:
{
size_t v_i_boxed_4779_; size_t v_stop_boxed_4780_; uint8_t v_res_4781_; lean_object* v_r_4782_; 
v_i_boxed_4779_ = lean_unbox_usize(v_i_4777_);
lean_dec(v_i_4777_);
v_stop_boxed_4780_ = lean_unbox_usize(v_stop_4778_);
lean_dec(v_stop_4778_);
v_res_4781_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4774_, v___x_4775_, v_as_4776_, v_i_boxed_4779_, v_stop_boxed_4780_);
lean_dec_ref(v_as_4776_);
lean_dec(v___x_4775_);
lean_dec(v_alt_4774_);
v_r_4782_ = lean_box(v_res_4781_);
return v_r_4782_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4783_){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4784_ = lean_unsigned_to_nat(0u);
v___x_4785_ = lean_array_get_size(v_alts_4783_);
v___x_4786_ = lean_nat_dec_lt(v___x_4784_, v___x_4785_);
if (v___x_4786_ == 0)
{
uint8_t v___x_4787_; 
v___x_4787_ = 1;
return v___x_4787_;
}
else
{
lean_object* v_alt_4788_; uint8_t v___x_4789_; 
v_alt_4788_ = lean_array_fget_borrowed(v_alts_4783_, v___x_4784_);
lean_inc(v_alt_4788_);
v___x_4789_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4788_);
if (v___x_4789_ == 0)
{
return v___x_4789_;
}
else
{
if (v___x_4786_ == 0)
{
return v___x_4786_;
}
else
{
if (v___x_4786_ == 0)
{
return v___x_4786_;
}
else
{
size_t v___x_4790_; size_t v___x_4791_; uint8_t v___x_4792_; 
v___x_4790_ = ((size_t)0ULL);
v___x_4791_ = lean_usize_of_nat(v___x_4785_);
v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4788_, v___x_4785_, v_alts_4783_, v___x_4790_, v___x_4791_);
if (v___x_4792_ == 0)
{
return v___x_4786_;
}
else
{
uint8_t v___x_4793_; 
v___x_4793_ = 0;
return v___x_4793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4794_){
_start:
{
uint8_t v_res_4795_; lean_object* v_r_4796_; 
v_res_4795_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4794_);
lean_dec_ref(v_alts_4794_);
v_r_4796_ = lean_box(v_res_4795_);
return v_r_4796_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4804_){
_start:
{
if (lean_obj_tag(v_alt_4804_) == 1)
{
lean_object* v_tail_4805_; 
v_tail_4805_ = lean_ctor_get(v_alt_4804_, 1);
if (lean_obj_tag(v_tail_4805_) == 0)
{
lean_object* v_head_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v_head_4806_ = lean_ctor_get(v_alt_4804_, 0);
lean_inc(v_head_4806_);
lean_dec_ref_known(v_alt_4804_, 2);
v___x_4807_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4808_ = l_Lean_Syntax_isOfKind(v_head_4806_, v___x_4807_);
return v___x_4808_;
}
else
{
uint8_t v___x_4809_; 
lean_dec_ref_known(v_alt_4804_, 2);
v___x_4809_ = 0;
return v___x_4809_;
}
}
else
{
uint8_t v___x_4810_; 
lean_dec(v_alt_4804_);
v___x_4810_ = 0;
return v___x_4810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4811_){
_start:
{
uint8_t v_res_4812_; lean_object* v_r_4813_; 
v_res_4812_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4811_);
v_r_4813_ = lean_box(v_res_4812_);
return v_r_4813_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4814_, lean_object* v_x_4815_, lean_object* v___y_4816_){
_start:
{
if (lean_obj_tag(v_x_4814_) == 0)
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = l_List_reverse___redArg(v_x_4815_);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
return v___x_4819_;
}
else
{
lean_object* v_head_4820_; lean_object* v_tail_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4839_; 
v_head_4820_ = lean_ctor_get(v_x_4814_, 0);
v_tail_4821_ = lean_ctor_get(v_x_4814_, 1);
v_isSharedCheck_4839_ = !lean_is_exclusive(v_x_4814_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4823_ = v_x_4814_;
v_isShared_4824_ = v_isSharedCheck_4839_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_tail_4821_);
lean_inc(v_head_4820_);
lean_dec(v_x_4814_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4839_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4825_; 
v___x_4825_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4820_, v___y_4816_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4828_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v___x_4825_, 1);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 1, v_x_4815_);
lean_ctor_set(v___x_4823_, 0, v_a_4826_);
v___x_4828_ = v___x_4823_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4826_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_x_4815_);
v___x_4828_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
v_x_4814_ = v_tail_4821_;
v_x_4815_ = v___x_4828_;
goto _start;
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
lean_del_object(v___x_4823_);
lean_dec(v_tail_4821_);
lean_dec(v_x_4815_);
v_a_4831_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4825_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4825_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4840_, lean_object* v_x_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4840_, v_x_4841_, v___y_4842_);
lean_dec_ref(v___y_4842_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4845_, lean_object* v_alts_4846_, uint8_t v_compress_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_seq_4852_; 
if (v_compress_4847_ == 0)
{
goto v___jp_4855_;
}
else
{
uint8_t v___x_4865_; 
v___x_4865_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4846_);
if (v___x_4865_ == 0)
{
goto v___jp_4855_;
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; 
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = lean_array_get_size(v_alts_4846_);
v___x_4868_ = lean_nat_dec_lt(v___x_4866_, v___x_4867_);
if (v___x_4868_ == 0)
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec_ref(v_alts_4846_);
v___x_4869_ = lean_box(0);
v___x_4870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4870_, 0, v_cases_4845_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
return v___x_4871_;
}
else
{
lean_object* v___x_4872_; lean_object* v_firstAlt_4873_; uint8_t v___x_4874_; 
v___x_4872_ = lean_box(0);
v_firstAlt_4873_ = lean_array_get(v___x_4872_, v_alts_4846_, v___x_4866_);
lean_dec_ref(v_alts_4846_);
lean_inc(v_firstAlt_4873_);
v___x_4874_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4873_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4884_; 
v___x_4875_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4845_, v_firstAlt_4873_, v_a_4848_);
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4884_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4884_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4880_, 0, v_a_4876_);
lean_ctor_set(v___x_4880_, 1, v___x_4872_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4880_);
v___x_4882_ = v___x_4878_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
else
{
lean_object* v___x_4885_; 
lean_dec(v_cases_4845_);
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_firstAlt_4873_);
return v___x_4885_;
}
}
}
}
v___jp_4851_:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4853_, 0, v_cases_4845_);
lean_ctor_set(v___x_4853_, 1, v_seq_4852_);
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
return v___x_4854_;
}
v___jp_4855_:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4856_ = lean_array_get_size(v_alts_4846_);
v___x_4857_ = lean_unsigned_to_nat(1u);
v___x_4858_ = lean_nat_dec_eq(v___x_4856_, v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4859_ = lean_array_to_list(v_alts_4846_);
v___x_4860_ = lean_box(0);
v___x_4861_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4859_, v___x_4860_, v_a_4848_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v_seq_4852_ = v_a_4862_;
goto v___jp_4851_;
}
else
{
lean_dec(v_cases_4845_);
return v___x_4861_;
}
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = lean_array_fget(v_alts_4846_, v___x_4863_);
lean_dec_ref(v_alts_4846_);
v_seq_4852_ = v___x_4864_;
goto v___jp_4851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4886_, lean_object* v_alts_4887_, lean_object* v_compress_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
uint8_t v_compress_boxed_4892_; lean_object* v_res_4893_; 
v_compress_boxed_4892_ = lean_unbox(v_compress_4888_);
v_res_4893_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4886_, v_alts_4887_, v_compress_boxed_4892_, v_a_4889_, v_a_4890_);
lean_dec(v_a_4890_);
lean_dec_ref(v_a_4889_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4894_, lean_object* v_x_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4894_, v_x_4895_, v___y_4896_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4900_, lean_object* v_x_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4900_, v_x_4901_, v___y_4902_, v___y_4903_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___x_4909_; lean_object* v_env_4910_; uint8_t v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4909_ = lean_st_ref_get(v___y_4907_);
v_env_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc_ref(v_env_4910_);
lean_dec(v___x_4909_);
v___x_4911_ = l_Lean_Meta_isMatcherAppCore(v_env_4910_, v_e_4906_);
v___x_4912_ = lean_box(v___x_4911_);
v___x_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4914_, v___y_4915_);
lean_dec(v___y_4915_);
lean_dec_ref(v_e_4914_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v___x_4930_; 
v___x_4930_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4918_, v___y_4928_);
return v___x_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec(v___y_4932_);
lean_dec_ref(v_e_4931_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v___x_4955_; 
lean_inc(v___y_4949_);
lean_inc_ref(v___y_4948_);
lean_inc(v___y_4947_);
lean_inc_ref(v___y_4946_);
lean_inc(v___y_4945_);
v___x_4955_ = lean_apply_10(v_x_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, lean_box(0));
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4968_, lean_object* v_x_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___f_4980_; lean_object* v___x_4981_; 
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
lean_inc(v___y_4972_);
lean_inc_ref(v___y_4971_);
lean_inc(v___y_4970_);
v___f_4980_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4980_, 0, v_x_4969_);
lean_closure_set(v___f_4980_, 1, v___y_4970_);
lean_closure_set(v___f_4980_, 2, v___y_4971_);
lean_closure_set(v___f_4980_, 3, v___y_4972_);
lean_closure_set(v___f_4980_, 4, v___y_4973_);
lean_closure_set(v___f_4980_, 5, v___y_4974_);
v___x_4981_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4968_, v___f_4980_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_);
if (lean_obj_tag(v___x_4981_) == 0)
{
return v___x_4981_;
}
else
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4984_ = v___x_4981_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4981_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_4990_, lean_object* v_x_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4990_, v_x_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5003_, lean_object* v_mvarId_5004_, lean_object* v_x_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5004_, v_x_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5017_, lean_object* v_mvarId_5018_, lean_object* v_x_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5017_, v_mvarId_5018_, v_x_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
return v_res_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5031_, lean_object* v___y_5032_){
_start:
{
uint8_t v___x_5034_; 
v___x_5034_ = l_Lean_Expr_hasMVar(v_e_5031_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; 
v___x_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5035_, 0, v_e_5031_);
return v___x_5035_;
}
else
{
lean_object* v___x_5036_; lean_object* v_mctx_5037_; lean_object* v___x_5038_; lean_object* v_fst_5039_; lean_object* v_snd_5040_; lean_object* v___x_5041_; lean_object* v_cache_5042_; lean_object* v_zetaDeltaFVarIds_5043_; lean_object* v_postponed_5044_; lean_object* v_diag_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5054_; 
v___x_5036_ = lean_st_ref_get(v___y_5032_);
v_mctx_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc_ref(v_mctx_5037_);
lean_dec(v___x_5036_);
v___x_5038_ = l_Lean_instantiateMVarsCore(v_mctx_5037_, v_e_5031_);
v_fst_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_fst_5039_);
v_snd_5040_ = lean_ctor_get(v___x_5038_, 1);
lean_inc(v_snd_5040_);
lean_dec_ref(v___x_5038_);
v___x_5041_ = lean_st_ref_take(v___y_5032_);
v_cache_5042_ = lean_ctor_get(v___x_5041_, 1);
v_zetaDeltaFVarIds_5043_ = lean_ctor_get(v___x_5041_, 2);
v_postponed_5044_ = lean_ctor_get(v___x_5041_, 3);
v_diag_5045_ = lean_ctor_get(v___x_5041_, 4);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5054_ == 0)
{
lean_object* v_unused_5055_; 
v_unused_5055_ = lean_ctor_get(v___x_5041_, 0);
lean_dec(v_unused_5055_);
v___x_5047_ = v___x_5041_;
v_isShared_5048_ = v_isSharedCheck_5054_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_diag_5045_);
lean_inc(v_postponed_5044_);
lean_inc(v_zetaDeltaFVarIds_5043_);
lean_inc(v_cache_5042_);
lean_dec(v___x_5041_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5054_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v_snd_5040_);
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_snd_5040_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v_cache_5042_);
lean_ctor_set(v_reuseFailAlloc_5053_, 2, v_zetaDeltaFVarIds_5043_);
lean_ctor_set(v_reuseFailAlloc_5053_, 3, v_postponed_5044_);
lean_ctor_set(v_reuseFailAlloc_5053_, 4, v_diag_5045_);
v___x_5050_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5051_ = lean_st_ref_put(v___y_5032_, v___x_5050_);
v___x_5052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5052_, 0, v_fst_5039_);
return v___x_5052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5056_, v___y_5057_);
lean_dec(v___y_5057_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v___x_5071_; 
v___x_5071_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5060_, v___y_5067_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
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
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5086_ = l_Lean_stringToMessageData(v___x_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5087_, lean_object* v_c_5088_, lean_object* v_a_5089_, lean_object* v_numCases_5090_, uint8_t v_isRec_5091_, lean_object* v_anchorInfo_x3f_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
lean_object* v_mvarIds_5105_; lean_object* v___x_5155_; 
v___x_5155_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5087_, v___y_5093_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___y_5158_; lean_object* v___x_5210_; uint8_t v___x_5213_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
lean_dec_ref_known(v___x_5155_, 1);
v___x_5210_ = lean_unsigned_to_nat(1u);
v___x_5213_ = lean_nat_dec_lt(v___x_5210_, v_numCases_5090_);
if (v___x_5213_ == 0)
{
if (v_isRec_5091_ == 0)
{
lean_inc(v_a_5156_);
v___y_5158_ = v_a_5156_;
goto v___jp_5157_;
}
else
{
goto v___jp_5211_;
}
}
else
{
goto v___jp_5211_;
}
v___jp_5157_:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5159_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5088_);
lean_inc_ref(v___x_5087_);
v___x_5160_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5087_, v___y_5158_, v_numCases_5090_, v___x_5159_, v___y_5096_, v___y_5099_, v___y_5101_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v___x_5161_; 
lean_dec_ref_known(v___x_5160_, 1);
lean_inc_ref(v___x_5087_);
v___x_5161_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5087_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_toCold_5162_; lean_object* v_options_5163_; uint8_t v_hasTrace_5164_; 
lean_dec_ref_known(v___x_5161_, 1);
v_toCold_5162_ = lean_ctor_get(v___y_5101_, 0);
v_options_5163_ = lean_ctor_get(v_toCold_5162_, 2);
v_hasTrace_5164_ = lean_ctor_get_uint8(v_options_5163_, sizeof(void*)*1);
if (v_hasTrace_5164_ == 0)
{
lean_dec(v_a_5156_);
goto v___jp_5108_;
}
else
{
lean_object* v_inheritedTraceOptions_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; uint8_t v___x_5168_; 
v_inheritedTraceOptions_5165_ = lean_ctor_get(v_toCold_5162_, 11);
v___x_5166_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5167_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5165_, v_options_5163_, v___x_5167_);
if (v___x_5168_ == 0)
{
lean_dec(v_a_5156_);
goto v___jp_5108_;
}
else
{
lean_object* v___x_5169_; 
v___x_5169_ = l_Lean_Meta_Grind_updateLastTag(v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
lean_dec_ref_known(v___x_5169_, 1);
lean_inc_ref(v___x_5087_);
v___x_5170_ = l_Lean_MessageData_ofExpr(v___x_5087_);
v___x_5171_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5170_);
lean_ctor_set(v___x_5172_, 1, v___x_5171_);
v___x_5173_ = l_Nat_reprFast(v_a_5156_);
v___x_5174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5174_, 0, v___x_5173_);
v___x_5175_ = l_Lean_MessageData_ofFormat(v___x_5174_);
v___x_5176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5172_);
lean_ctor_set(v___x_5176_, 1, v___x_5175_);
v___x_5177_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5166_, v___x_5176_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_dec_ref_known(v___x_5177_, 1);
goto v___jp_5108_;
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
lean_dec(v_anchorInfo_x3f_5092_);
lean_dec(v_a_5089_);
lean_dec_ref(v_c_5088_);
lean_dec_ref(v___x_5087_);
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5177_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5177_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
lean_dec(v_a_5156_);
lean_dec(v_anchorInfo_x3f_5092_);
lean_dec(v_a_5089_);
lean_dec_ref(v_c_5088_);
lean_dec_ref(v___x_5087_);
v_a_5186_ = lean_ctor_get(v___x_5169_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5169_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5169_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5169_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
}
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec(v_a_5156_);
lean_dec(v_anchorInfo_x3f_5092_);
lean_dec(v_a_5089_);
lean_dec_ref(v_c_5088_);
lean_dec_ref(v___x_5087_);
v_a_5194_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5161_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5161_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_dec(v_a_5156_);
lean_dec(v_anchorInfo_x3f_5092_);
lean_dec(v_a_5089_);
lean_dec_ref(v_c_5088_);
lean_dec_ref(v___x_5087_);
v_a_5202_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5160_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5160_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
v___jp_5211_:
{
lean_object* v___x_5212_; 
v___x_5212_ = lean_nat_add(v_a_5156_, v___x_5210_);
v___y_5158_ = v___x_5212_;
goto v___jp_5157_;
}
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
lean_dec(v_anchorInfo_x3f_5092_);
lean_dec(v_numCases_5090_);
lean_dec(v_a_5089_);
lean_dec_ref(v_c_5088_);
lean_dec_ref(v___x_5087_);
v_a_5214_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5155_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5155_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
v___x_5219_ = v___x_5216_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_a_5214_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
v___jp_5104_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5106_, 0, v_mvarIds_5105_);
lean_ctor_set(v___x_5106_, 1, v_anchorInfo_x3f_5092_);
v___x_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
return v___x_5107_;
}
v___jp_5108_:
{
lean_object* v___x_5109_; 
v___x_5109_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5087_, v___y_5102_);
if (lean_obj_tag(v_c_5088_) == 1)
{
lean_object* v_e_5110_; lean_object* v_binderType_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
lean_dec_ref(v___x_5109_);
lean_dec_ref(v___x_5087_);
v_e_5110_ = lean_ctor_get(v_c_5088_, 0);
lean_inc_ref(v_e_5110_);
lean_dec_ref_known(v_c_5088_, 2);
v_binderType_5111_ = lean_ctor_get(v_e_5110_, 1);
lean_inc_ref(v_binderType_5111_);
lean_dec_ref(v_e_5110_);
v___x_5112_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5111_);
v___x_5113_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5089_, v___x_5112_, v___y_5095_, v___y_5096_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5114_);
lean_dec_ref_known(v___x_5113_, 1);
v_mvarIds_5105_ = v_a_5114_;
goto v___jp_5104_;
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_dec(v_anchorInfo_x3f_5092_);
v_a_5115_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5113_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5113_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
else
{
lean_object* v_a_5123_; uint8_t v___x_5124_; 
lean_dec_ref(v_c_5088_);
v_a_5123_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_a_5123_);
lean_dec_ref(v___x_5109_);
v___x_5124_ = lean_unbox(v_a_5123_);
lean_dec(v_a_5123_);
if (v___x_5124_ == 0)
{
lean_object* v___x_5125_; 
v___x_5125_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5087_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5127_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5125_, 1);
v___x_5127_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5089_, v_a_5126_, v___y_5095_, v___y_5096_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5127_, 1);
v_mvarIds_5105_ = v_a_5128_;
goto v___jp_5104_;
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5136_; 
lean_dec(v_anchorInfo_x3f_5092_);
v_a_5129_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5131_ = v___x_5127_;
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___x_5127_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_dec(v_anchorInfo_x3f_5092_);
lean_dec(v_a_5089_);
v_a_5137_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5125_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5125_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
else
{
lean_object* v___x_5145_; 
v___x_5145_ = l_Lean_Meta_Grind_casesMatch(v_a_5089_, v___x_5087_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___x_5145_, 1);
v_mvarIds_5105_ = v_a_5146_;
goto v___jp_5104_;
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec(v_anchorInfo_x3f_5092_);
v_a_5147_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5145_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5145_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5222_ = _args[0];
lean_object* v_c_5223_ = _args[1];
lean_object* v_a_5224_ = _args[2];
lean_object* v_numCases_5225_ = _args[3];
lean_object* v_isRec_5226_ = _args[4];
lean_object* v_anchorInfo_x3f_5227_ = _args[5];
lean_object* v___y_5228_ = _args[6];
lean_object* v___y_5229_ = _args[7];
lean_object* v___y_5230_ = _args[8];
lean_object* v___y_5231_ = _args[9];
lean_object* v___y_5232_ = _args[10];
lean_object* v___y_5233_ = _args[11];
lean_object* v___y_5234_ = _args[12];
lean_object* v___y_5235_ = _args[13];
lean_object* v___y_5236_ = _args[14];
lean_object* v___y_5237_ = _args[15];
lean_object* v___y_5238_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5239_; lean_object* v_res_5240_; 
v_isRec_boxed_5239_ = lean_unbox(v_isRec_5226_);
v_res_5240_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5222_, v_c_5223_, v_a_5224_, v_numCases_5225_, v_isRec_boxed_5239_, v_anchorInfo_x3f_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec(v___y_5228_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5241_, uint8_t v_trace_5242_, lean_object* v___f_5243_, lean_object* v_c_5244_, lean_object* v_candidates_x3f_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v___x_5256_; lean_object* v___y_5258_; 
v___x_5256_ = lean_st_mk_ref(v_goal_5241_);
if (v_trace_5242_ == 0)
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
lean_dec(v_candidates_x3f_5245_);
v___x_5277_ = lean_box(0);
lean_inc(v___x_5256_);
v___x_5278_ = lean_apply_12(v___f_5243_, v___x_5277_, v___x_5256_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, lean_box(0));
v___y_5258_ = v___x_5278_;
goto v___jp_5257_;
}
else
{
lean_object* v___x_5279_; 
v___x_5279_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5244_, v_candidates_x3f_5245_, v___x_5256_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v___x_5279_, 1);
v___x_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5281_, 0, v_a_5280_);
lean_inc(v___x_5256_);
v___x_5282_ = lean_apply_12(v___f_5243_, v___x_5281_, v___x_5256_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, lean_box(0));
v___y_5258_ = v___x_5282_;
goto v___jp_5257_;
}
else
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5290_; 
lean_dec(v___x_5256_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___f_5243_);
v_a_5283_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5285_ = v___x_5279_;
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5279_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5288_; 
if (v_isShared_5286_ == 0)
{
v___x_5288_ = v___x_5285_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_a_5283_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
}
v___jp_5257_:
{
if (lean_obj_tag(v___y_5258_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5268_; 
v_a_5259_ = lean_ctor_get(v___y_5258_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___y_5258_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5261_ = v___y_5258_;
v_isShared_5262_ = v_isSharedCheck_5268_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___y_5258_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5268_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5266_; 
v___x_5263_ = lean_st_ref_get(v___x_5256_);
lean_dec(v___x_5256_);
v___x_5264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5264_, 0, v_a_5259_);
lean_ctor_set(v___x_5264_, 1, v___x_5263_);
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 0, v___x_5264_);
v___x_5266_ = v___x_5261_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5264_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec(v___x_5256_);
v_a_5269_ = lean_ctor_get(v___y_5258_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___y_5258_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___y_5258_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___y_5258_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5291_, lean_object* v_trace_5292_, lean_object* v___f_5293_, lean_object* v_c_5294_, lean_object* v_candidates_x3f_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
uint8_t v_trace_boxed_5306_; lean_object* v_res_5307_; 
v_trace_boxed_5306_ = lean_unbox(v_trace_5292_);
v_res_5307_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5291_, v_trace_boxed_5306_, v___f_5293_, v_c_5294_, v_candidates_x3f_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec_ref(v_c_5294_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5308_, lean_object* v_x_5309_, lean_object* v_x_5310_, lean_object* v_x_5311_){
_start:
{
lean_object* v_ks_5312_; lean_object* v_vs_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5337_; 
v_ks_5312_ = lean_ctor_get(v_x_5308_, 0);
v_vs_5313_ = lean_ctor_get(v_x_5308_, 1);
v_isSharedCheck_5337_ = !lean_is_exclusive(v_x_5308_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5315_ = v_x_5308_;
v_isShared_5316_ = v_isSharedCheck_5337_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_vs_5313_);
lean_inc(v_ks_5312_);
lean_dec(v_x_5308_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5337_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5317_; uint8_t v___x_5318_; 
v___x_5317_ = lean_array_get_size(v_ks_5312_);
v___x_5318_ = lean_nat_dec_lt(v_x_5309_, v___x_5317_);
if (v___x_5318_ == 0)
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5322_; 
lean_dec(v_x_5309_);
v___x_5319_ = lean_array_push(v_ks_5312_, v_x_5310_);
v___x_5320_ = lean_array_push(v_vs_5313_, v_x_5311_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 1, v___x_5320_);
lean_ctor_set(v___x_5315_, 0, v___x_5319_);
v___x_5322_ = v___x_5315_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5319_);
lean_ctor_set(v_reuseFailAlloc_5323_, 1, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
else
{
lean_object* v_k_x27_5324_; uint8_t v___x_5325_; 
v_k_x27_5324_ = lean_array_fget_borrowed(v_ks_5312_, v_x_5309_);
v___x_5325_ = l_Lean_instBEqMVarId_beq(v_x_5310_, v_k_x27_5324_);
if (v___x_5325_ == 0)
{
lean_object* v___x_5327_; 
if (v_isShared_5316_ == 0)
{
v___x_5327_ = v___x_5315_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_ks_5312_);
lean_ctor_set(v_reuseFailAlloc_5331_, 1, v_vs_5313_);
v___x_5327_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; 
v___x_5328_ = lean_unsigned_to_nat(1u);
v___x_5329_ = lean_nat_add(v_x_5309_, v___x_5328_);
lean_dec(v_x_5309_);
v_x_5308_ = v___x_5327_;
v_x_5309_ = v___x_5329_;
goto _start;
}
}
else
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5332_ = lean_array_fset(v_ks_5312_, v_x_5309_, v_x_5310_);
v___x_5333_ = lean_array_fset(v_vs_5313_, v_x_5309_, v_x_5311_);
lean_dec(v_x_5309_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 1, v___x_5333_);
lean_ctor_set(v___x_5315_, 0, v___x_5332_);
v___x_5335_ = v___x_5315_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5332_);
lean_ctor_set(v_reuseFailAlloc_5336_, 1, v___x_5333_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5338_, lean_object* v_k_5339_, lean_object* v_v_5340_){
_start:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5341_ = lean_unsigned_to_nat(0u);
v___x_5342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5338_, v___x_5341_, v_k_5339_, v_v_5340_);
return v___x_5342_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5343_; 
v___x_5343_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_5343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5344_, size_t v_x_5345_, size_t v_x_5346_, lean_object* v_x_5347_, lean_object* v_x_5348_){
_start:
{
if (lean_obj_tag(v_x_5344_) == 0)
{
lean_object* v_es_5349_; size_t v___x_5350_; size_t v___x_5351_; lean_object* v_j_5352_; lean_object* v___x_5353_; uint8_t v___x_5354_; 
v_es_5349_ = lean_ctor_get(v_x_5344_, 0);
v___x_5350_ = ((size_t)31ULL);
v___x_5351_ = lean_usize_land(v_x_5345_, v___x_5350_);
v_j_5352_ = lean_usize_to_nat(v___x_5351_);
v___x_5353_ = lean_array_get_size(v_es_5349_);
v___x_5354_ = lean_nat_dec_lt(v_j_5352_, v___x_5353_);
if (v___x_5354_ == 0)
{
lean_dec(v_j_5352_);
lean_dec(v_x_5348_);
lean_dec(v_x_5347_);
return v_x_5344_;
}
else
{
lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5393_; 
lean_inc_ref(v_es_5349_);
v_isSharedCheck_5393_ = !lean_is_exclusive(v_x_5344_);
if (v_isSharedCheck_5393_ == 0)
{
lean_object* v_unused_5394_; 
v_unused_5394_ = lean_ctor_get(v_x_5344_, 0);
lean_dec(v_unused_5394_);
v___x_5356_ = v_x_5344_;
v_isShared_5357_ = v_isSharedCheck_5393_;
goto v_resetjp_5355_;
}
else
{
lean_dec(v_x_5344_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5393_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v_v_5358_; lean_object* v___x_5359_; lean_object* v_xs_x27_5360_; lean_object* v___y_5362_; 
v_v_5358_ = lean_array_fget(v_es_5349_, v_j_5352_);
v___x_5359_ = lean_box(0);
v_xs_x27_5360_ = lean_array_fset(v_es_5349_, v_j_5352_, v___x_5359_);
switch(lean_obj_tag(v_v_5358_))
{
case 0:
{
lean_object* v_key_5367_; lean_object* v_val_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5378_; 
v_key_5367_ = lean_ctor_get(v_v_5358_, 0);
v_val_5368_ = lean_ctor_get(v_v_5358_, 1);
v_isSharedCheck_5378_ = !lean_is_exclusive(v_v_5358_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5370_ = v_v_5358_;
v_isShared_5371_ = v_isSharedCheck_5378_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_val_5368_);
lean_inc(v_key_5367_);
lean_dec(v_v_5358_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5378_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
uint8_t v___x_5372_; 
v___x_5372_ = l_Lean_instBEqMVarId_beq(v_x_5347_, v_key_5367_);
if (v___x_5372_ == 0)
{
lean_object* v___x_5373_; lean_object* v___x_5374_; 
lean_del_object(v___x_5370_);
v___x_5373_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5367_, v_val_5368_, v_x_5347_, v_x_5348_);
v___x_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5373_);
v___y_5362_ = v___x_5374_;
goto v___jp_5361_;
}
else
{
lean_object* v___x_5376_; 
lean_dec(v_val_5368_);
lean_dec(v_key_5367_);
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 1, v_x_5348_);
lean_ctor_set(v___x_5370_, 0, v_x_5347_);
v___x_5376_ = v___x_5370_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_x_5347_);
lean_ctor_set(v_reuseFailAlloc_5377_, 1, v_x_5348_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
v___y_5362_ = v___x_5376_;
goto v___jp_5361_;
}
}
}
}
case 1:
{
lean_object* v_node_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5391_; 
v_node_5379_ = lean_ctor_get(v_v_5358_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v_v_5358_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5381_ = v_v_5358_;
v_isShared_5382_ = v_isSharedCheck_5391_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_node_5379_);
lean_dec(v_v_5358_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5391_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
size_t v___x_5383_; size_t v___x_5384_; size_t v___x_5385_; size_t v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5389_; 
v___x_5383_ = ((size_t)5ULL);
v___x_5384_ = lean_usize_shift_right(v_x_5345_, v___x_5383_);
v___x_5385_ = ((size_t)1ULL);
v___x_5386_ = lean_usize_add(v_x_5346_, v___x_5385_);
v___x_5387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5379_, v___x_5384_, v___x_5386_, v_x_5347_, v_x_5348_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 0, v___x_5387_);
v___x_5389_ = v___x_5381_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5387_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
v___y_5362_ = v___x_5389_;
goto v___jp_5361_;
}
}
}
default: 
{
lean_object* v___x_5392_; 
v___x_5392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5392_, 0, v_x_5347_);
lean_ctor_set(v___x_5392_, 1, v_x_5348_);
v___y_5362_ = v___x_5392_;
goto v___jp_5361_;
}
}
v___jp_5361_:
{
lean_object* v___x_5363_; lean_object* v___x_5365_; 
v___x_5363_ = lean_array_fset(v_xs_x27_5360_, v_j_5352_, v___y_5362_);
lean_dec(v_j_5352_);
if (v_isShared_5357_ == 0)
{
lean_ctor_set(v___x_5356_, 0, v___x_5363_);
v___x_5365_ = v___x_5356_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5363_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
else
{
lean_object* v_ks_5395_; lean_object* v_vs_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5414_; 
v_ks_5395_ = lean_ctor_get(v_x_5344_, 0);
v_vs_5396_ = lean_ctor_get(v_x_5344_, 1);
v_isSharedCheck_5414_ = !lean_is_exclusive(v_x_5344_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5398_ = v_x_5344_;
v_isShared_5399_ = v_isSharedCheck_5414_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_vs_5396_);
lean_inc(v_ks_5395_);
lean_dec(v_x_5344_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5414_;
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
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_ks_5395_);
lean_ctor_set(v_reuseFailAlloc_5413_, 1, v_vs_5396_);
v___x_5401_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v_newNode_5402_; size_t v___x_5403_; uint8_t v___x_5404_; 
v_newNode_5402_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5401_, v_x_5347_, v_x_5348_);
v___x_5403_ = ((size_t)7ULL);
v___x_5404_ = lean_usize_dec_le(v___x_5403_, v_x_5346_);
if (v___x_5404_ == 0)
{
lean_object* v___x_5405_; lean_object* v___x_5406_; uint8_t v___x_5407_; 
v___x_5405_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5402_);
v___x_5406_ = lean_unsigned_to_nat(4u);
v___x_5407_ = lean_nat_dec_lt(v___x_5405_, v___x_5406_);
lean_dec(v___x_5405_);
if (v___x_5407_ == 0)
{
lean_object* v_ks_5408_; lean_object* v_vs_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v_ks_5408_ = lean_ctor_get(v_newNode_5402_, 0);
lean_inc_ref(v_ks_5408_);
v_vs_5409_ = lean_ctor_get(v_newNode_5402_, 1);
lean_inc_ref(v_vs_5409_);
lean_dec_ref(v_newNode_5402_);
v___x_5410_ = lean_unsigned_to_nat(0u);
v___x_5411_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5412_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5346_, v_ks_5408_, v_vs_5409_, v___x_5410_, v___x_5411_);
lean_dec_ref(v_vs_5409_);
lean_dec_ref(v_ks_5408_);
return v___x_5412_;
}
else
{
return v_newNode_5402_;
}
}
else
{
return v_newNode_5402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5415_, lean_object* v_keys_5416_, lean_object* v_vals_5417_, lean_object* v_i_5418_, lean_object* v_entries_5419_){
_start:
{
lean_object* v___x_5420_; uint8_t v___x_5421_; 
v___x_5420_ = lean_array_get_size(v_keys_5416_);
v___x_5421_ = lean_nat_dec_lt(v_i_5418_, v___x_5420_);
if (v___x_5421_ == 0)
{
lean_dec(v_i_5418_);
return v_entries_5419_;
}
else
{
lean_object* v_k_5422_; lean_object* v_v_5423_; uint64_t v___x_5424_; size_t v_h_5425_; size_t v___x_5426_; lean_object* v___x_5427_; size_t v___x_5428_; size_t v___x_5429_; size_t v___x_5430_; size_t v_h_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v_k_5422_ = lean_array_fget_borrowed(v_keys_5416_, v_i_5418_);
v_v_5423_ = lean_array_fget_borrowed(v_vals_5417_, v_i_5418_);
v___x_5424_ = l_Lean_instHashableMVarId_hash(v_k_5422_);
v_h_5425_ = lean_uint64_to_usize(v___x_5424_);
v___x_5426_ = ((size_t)5ULL);
v___x_5427_ = lean_unsigned_to_nat(1u);
v___x_5428_ = ((size_t)1ULL);
v___x_5429_ = lean_usize_sub(v_depth_5415_, v___x_5428_);
v___x_5430_ = lean_usize_mul(v___x_5426_, v___x_5429_);
v_h_5431_ = lean_usize_shift_right(v_h_5425_, v___x_5430_);
v___x_5432_ = lean_nat_add(v_i_5418_, v___x_5427_);
lean_dec(v_i_5418_);
lean_inc(v_v_5423_);
lean_inc(v_k_5422_);
v___x_5433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5419_, v_h_5431_, v_depth_5415_, v_k_5422_, v_v_5423_);
v_i_5418_ = v___x_5432_;
v_entries_5419_ = v___x_5433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5435_, lean_object* v_keys_5436_, lean_object* v_vals_5437_, lean_object* v_i_5438_, lean_object* v_entries_5439_){
_start:
{
size_t v_depth_boxed_5440_; lean_object* v_res_5441_; 
v_depth_boxed_5440_ = lean_unbox_usize(v_depth_5435_);
lean_dec(v_depth_5435_);
v_res_5441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5440_, v_keys_5436_, v_vals_5437_, v_i_5438_, v_entries_5439_);
lean_dec_ref(v_vals_5437_);
lean_dec_ref(v_keys_5436_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5442_, lean_object* v_x_5443_, lean_object* v_x_5444_, lean_object* v_x_5445_, lean_object* v_x_5446_){
_start:
{
size_t v_x_66926__boxed_5447_; size_t v_x_66927__boxed_5448_; lean_object* v_res_5449_; 
v_x_66926__boxed_5447_ = lean_unbox_usize(v_x_5443_);
lean_dec(v_x_5443_);
v_x_66927__boxed_5448_ = lean_unbox_usize(v_x_5444_);
lean_dec(v_x_5444_);
v_res_5449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5442_, v_x_66926__boxed_5447_, v_x_66927__boxed_5448_, v_x_5445_, v_x_5446_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5450_, lean_object* v_x_5451_, lean_object* v_x_5452_){
_start:
{
uint64_t v___x_5453_; size_t v___x_5454_; size_t v___x_5455_; lean_object* v___x_5456_; 
v___x_5453_ = l_Lean_instHashableMVarId_hash(v_x_5451_);
v___x_5454_ = lean_uint64_to_usize(v___x_5453_);
v___x_5455_ = ((size_t)1ULL);
v___x_5456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5450_, v___x_5454_, v___x_5455_, v_x_5451_, v_x_5452_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5457_, lean_object* v_val_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v___x_5461_; lean_object* v_mctx_5462_; lean_object* v_cache_5463_; lean_object* v_zetaDeltaFVarIds_5464_; lean_object* v_postponed_5465_; lean_object* v_diag_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5496_; 
v___x_5461_ = lean_st_ref_take(v___y_5459_);
v_mctx_5462_ = lean_ctor_get(v___x_5461_, 0);
v_cache_5463_ = lean_ctor_get(v___x_5461_, 1);
v_zetaDeltaFVarIds_5464_ = lean_ctor_get(v___x_5461_, 2);
v_postponed_5465_ = lean_ctor_get(v___x_5461_, 3);
v_diag_5466_ = lean_ctor_get(v___x_5461_, 4);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5468_ = v___x_5461_;
v_isShared_5469_ = v_isSharedCheck_5496_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_diag_5466_);
lean_inc(v_postponed_5465_);
lean_inc(v_zetaDeltaFVarIds_5464_);
lean_inc(v_cache_5463_);
lean_inc(v_mctx_5462_);
lean_dec(v___x_5461_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5496_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v_depth_5470_; lean_object* v_levelAssignDepth_5471_; lean_object* v_lmvarCounter_5472_; lean_object* v_mvarCounter_5473_; lean_object* v_lDecls_5474_; lean_object* v_decls_5475_; lean_object* v_userNames_5476_; lean_object* v_lAssignment_5477_; lean_object* v_eAssignment_5478_; lean_object* v_dAssignment_5479_; lean_object* v_instanceTypedMVars_5480_; lean_object* v_synthNormMemo_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5495_; 
v_depth_5470_ = lean_ctor_get(v_mctx_5462_, 0);
v_levelAssignDepth_5471_ = lean_ctor_get(v_mctx_5462_, 1);
v_lmvarCounter_5472_ = lean_ctor_get(v_mctx_5462_, 2);
v_mvarCounter_5473_ = lean_ctor_get(v_mctx_5462_, 3);
v_lDecls_5474_ = lean_ctor_get(v_mctx_5462_, 4);
v_decls_5475_ = lean_ctor_get(v_mctx_5462_, 5);
v_userNames_5476_ = lean_ctor_get(v_mctx_5462_, 6);
v_lAssignment_5477_ = lean_ctor_get(v_mctx_5462_, 7);
v_eAssignment_5478_ = lean_ctor_get(v_mctx_5462_, 8);
v_dAssignment_5479_ = lean_ctor_get(v_mctx_5462_, 9);
v_instanceTypedMVars_5480_ = lean_ctor_get(v_mctx_5462_, 10);
v_synthNormMemo_5481_ = lean_ctor_get(v_mctx_5462_, 11);
v_isSharedCheck_5495_ = !lean_is_exclusive(v_mctx_5462_);
if (v_isSharedCheck_5495_ == 0)
{
v___x_5483_ = v_mctx_5462_;
v_isShared_5484_ = v_isSharedCheck_5495_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_synthNormMemo_5481_);
lean_inc(v_instanceTypedMVars_5480_);
lean_inc(v_dAssignment_5479_);
lean_inc(v_eAssignment_5478_);
lean_inc(v_lAssignment_5477_);
lean_inc(v_userNames_5476_);
lean_inc(v_decls_5475_);
lean_inc(v_lDecls_5474_);
lean_inc(v_mvarCounter_5473_);
lean_inc(v_lmvarCounter_5472_);
lean_inc(v_levelAssignDepth_5471_);
lean_inc(v_depth_5470_);
lean_dec(v_mctx_5462_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5495_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5488_; 
v___x_5485_ = lean_box(0);
v___x_5486_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5478_, v_mvarId_5457_, v_val_5458_);
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 8, v___x_5486_);
v___x_5488_ = v___x_5483_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_depth_5470_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v_levelAssignDepth_5471_);
lean_ctor_set(v_reuseFailAlloc_5494_, 2, v_lmvarCounter_5472_);
lean_ctor_set(v_reuseFailAlloc_5494_, 3, v_mvarCounter_5473_);
lean_ctor_set(v_reuseFailAlloc_5494_, 4, v_lDecls_5474_);
lean_ctor_set(v_reuseFailAlloc_5494_, 5, v_decls_5475_);
lean_ctor_set(v_reuseFailAlloc_5494_, 6, v_userNames_5476_);
lean_ctor_set(v_reuseFailAlloc_5494_, 7, v_lAssignment_5477_);
lean_ctor_set(v_reuseFailAlloc_5494_, 8, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5494_, 9, v_dAssignment_5479_);
lean_ctor_set(v_reuseFailAlloc_5494_, 10, v_instanceTypedMVars_5480_);
lean_ctor_set(v_reuseFailAlloc_5494_, 11, v_synthNormMemo_5481_);
v___x_5488_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5490_; 
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v___x_5488_);
v___x_5490_ = v___x_5468_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5488_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_cache_5463_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_zetaDeltaFVarIds_5464_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_postponed_5465_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_diag_5466_);
v___x_5490_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5491_ = lean_st_ref_put(v___y_5459_, v___x_5490_);
v___x_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5485_);
return v___x_5492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5497_, lean_object* v_val_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_){
_start:
{
lean_object* v_res_5501_; 
v_res_5501_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5497_, v_val_5498_, v___y_5499_);
lean_dec(v___y_5499_);
return v_res_5501_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5502_, lean_object* v_snd_5503_, uint8_t v_stopAtFirstFailure_5504_, lean_object* v_as_x27_5505_, lean_object* v_b_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_){
_start:
{
if (lean_obj_tag(v_as_x27_5505_) == 0)
{
lean_object* v___x_5517_; 
lean_dec_ref(v_snd_5503_);
lean_dec_ref(v_kp_5502_);
v___x_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5517_, 0, v_b_5506_);
return v___x_5517_;
}
else
{
lean_object* v_snd_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5624_; 
v_snd_5518_ = lean_ctor_get(v_b_5506_, 1);
v_isSharedCheck_5624_ = !lean_is_exclusive(v_b_5506_);
if (v_isSharedCheck_5624_ == 0)
{
lean_object* v_unused_5625_; 
v_unused_5625_ = lean_ctor_get(v_b_5506_, 0);
lean_dec(v_unused_5625_);
v___x_5520_ = v_b_5506_;
v_isShared_5521_ = v_isSharedCheck_5624_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_snd_5518_);
lean_dec(v_b_5506_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5624_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v_head_5522_; lean_object* v_tail_5523_; lean_object* v_fst_5524_; lean_object* v_snd_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5623_; 
v_head_5522_ = lean_ctor_get(v_as_x27_5505_, 0);
v_tail_5523_ = lean_ctor_get(v_as_x27_5505_, 1);
v_fst_5524_ = lean_ctor_get(v_snd_5518_, 0);
v_snd_5525_ = lean_ctor_get(v_snd_5518_, 1);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_snd_5518_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5527_ = v_snd_5518_;
v_isShared_5528_ = v_isSharedCheck_5623_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_snd_5525_);
lean_inc(v_fst_5524_);
lean_dec(v_snd_5518_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5623_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5529_ = lean_box(0);
lean_inc_ref(v_kp_5502_);
lean_inc(v___y_5515_);
lean_inc_ref(v___y_5514_);
lean_inc(v___y_5513_);
lean_inc_ref(v___y_5512_);
lean_inc(v___y_5511_);
lean_inc_ref(v___y_5510_);
lean_inc(v___y_5509_);
lean_inc_ref(v___y_5508_);
lean_inc(v___y_5507_);
lean_inc(v_head_5522_);
v___x_5530_ = lean_apply_11(v_kp_5502_, v_head_5522_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, lean_box(0));
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5614_; 
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5533_ = v___x_5530_;
v_isShared_5534_ = v_isSharedCheck_5614_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5530_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5614_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
if (lean_obj_tag(v_a_5531_) == 0)
{
lean_object* v_seq_5535_; lean_object* v_mvarId_5536_; lean_object* v___x_5537_; 
lean_del_object(v___x_5533_);
v_seq_5535_ = lean_ctor_get(v_a_5531_, 0);
v_mvarId_5536_ = lean_ctor_get(v_head_5522_, 1);
lean_inc(v_mvarId_5536_);
v___x_5537_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5536_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_object* v_a_5538_; 
v_a_5538_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_a_5538_);
lean_dec_ref_known(v___x_5537_, 1);
if (lean_obj_tag(v_a_5538_) == 1)
{
lean_object* v_val_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5570_; 
lean_dec_ref(v_kp_5502_);
v_val_5539_ = lean_ctor_get(v_a_5538_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v_a_5538_);
if (v_isSharedCheck_5570_ == 0)
{
v___x_5541_ = v_a_5538_;
v_isShared_5542_ = v_isSharedCheck_5570_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_val_5539_);
lean_dec(v_a_5538_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5570_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v_mvarId_5543_; lean_object* v___x_5544_; 
v_mvarId_5543_ = lean_ctor_get(v_snd_5503_, 1);
lean_inc(v_mvarId_5543_);
lean_dec_ref(v_snd_5503_);
v___x_5544_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5543_, v_val_5539_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5560_; 
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5560_ == 0)
{
lean_object* v_unused_5561_; 
v_unused_5561_ = lean_ctor_get(v___x_5544_, 0);
lean_dec(v_unused_5561_);
v___x_5546_ = v___x_5544_;
v_isShared_5547_ = v_isSharedCheck_5560_;
goto v_resetjp_5545_;
}
else
{
lean_dec(v___x_5544_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5560_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5542_ == 0)
{
lean_ctor_set(v___x_5541_, 0, v_a_5531_);
v___x_5549_ = v___x_5541_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_a_5531_);
v___x_5549_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5551_; 
if (v_isShared_5528_ == 0)
{
v___x_5551_ = v___x_5527_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_fst_5524_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v_snd_5525_);
v___x_5551_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5553_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 1, v___x_5551_);
lean_ctor_set(v___x_5520_, 0, v___x_5549_);
v___x_5553_ = v___x_5520_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5549_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5551_);
v___x_5553_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5555_; 
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5553_);
v___x_5555_ = v___x_5546_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5553_);
v___x_5555_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
return v___x_5555_;
}
}
}
}
}
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
lean_del_object(v___x_5541_);
lean_dec_ref_known(v_a_5531_, 1);
lean_del_object(v___x_5527_);
lean_dec(v_snd_5525_);
lean_dec(v_fst_5524_);
lean_del_object(v___x_5520_);
v_a_5562_ = lean_ctor_get(v___x_5544_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5564_ = v___x_5544_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5544_);
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
}
else
{
uint8_t v___x_5571_; 
lean_inc(v_seq_5535_);
lean_dec(v_a_5538_);
lean_dec_ref_known(v_a_5531_, 1);
v___x_5571_ = l_List_isEmpty___redArg(v_seq_5535_);
if (v___x_5571_ == 0)
{
lean_object* v___x_5572_; lean_object* v___x_5574_; 
v___x_5572_ = lean_array_push(v_fst_5524_, v_seq_5535_);
if (v_isShared_5528_ == 0)
{
lean_ctor_set(v___x_5527_, 0, v___x_5572_);
v___x_5574_ = v___x_5527_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5572_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v_snd_5525_);
v___x_5574_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
lean_object* v___x_5576_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 1, v___x_5574_);
lean_ctor_set(v___x_5520_, 0, v___x_5529_);
v___x_5576_ = v___x_5520_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5529_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v___x_5574_);
v___x_5576_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
v_as_x27_5505_ = v_tail_5523_;
v_b_5506_ = v___x_5576_;
goto _start;
}
}
}
else
{
lean_object* v___x_5581_; 
lean_dec(v_seq_5535_);
if (v_isShared_5528_ == 0)
{
v___x_5581_ = v___x_5527_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_fst_5524_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v_snd_5525_);
v___x_5581_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5583_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 1, v___x_5581_);
lean_ctor_set(v___x_5520_, 0, v___x_5529_);
v___x_5583_ = v___x_5520_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5529_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
v_as_x27_5505_ = v_tail_5523_;
v_b_5506_ = v___x_5583_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec_ref_known(v_a_5531_, 1);
lean_del_object(v___x_5527_);
lean_dec(v_snd_5525_);
lean_dec(v_fst_5524_);
lean_del_object(v___x_5520_);
lean_dec_ref(v_snd_5503_);
lean_dec_ref(v_kp_5502_);
v_a_5587_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5537_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5537_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5504_ == 0)
{
lean_object* v_gs_5595_; lean_object* v___x_5596_; lean_object* v___x_5598_; 
lean_del_object(v___x_5533_);
v_gs_5595_ = lean_ctor_get(v_a_5531_, 0);
lean_inc(v_gs_5595_);
lean_dec_ref_known(v_a_5531_, 1);
v___x_5596_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5525_, v_gs_5595_);
if (v_isShared_5528_ == 0)
{
lean_ctor_set(v___x_5527_, 1, v___x_5596_);
v___x_5598_ = v___x_5527_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_fst_5524_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v___x_5596_);
v___x_5598_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5600_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 1, v___x_5598_);
lean_ctor_set(v___x_5520_, 0, v___x_5529_);
v___x_5600_ = v___x_5520_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5529_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v___x_5598_);
v___x_5600_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
v_as_x27_5505_ = v_tail_5523_;
v_b_5506_ = v___x_5600_;
goto _start;
}
}
}
else
{
lean_object* v___x_5604_; lean_object* v___x_5606_; 
lean_dec_ref(v_snd_5503_);
lean_dec_ref(v_kp_5502_);
v___x_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5604_, 0, v_a_5531_);
if (v_isShared_5528_ == 0)
{
v___x_5606_ = v___x_5527_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_fst_5524_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_snd_5525_);
v___x_5606_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
lean_object* v___x_5608_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 1, v___x_5606_);
lean_ctor_set(v___x_5520_, 0, v___x_5604_);
v___x_5608_ = v___x_5520_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5604_);
lean_ctor_set(v_reuseFailAlloc_5612_, 1, v___x_5606_);
v___x_5608_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
lean_object* v___x_5610_; 
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 0, v___x_5608_);
v___x_5610_ = v___x_5533_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v___x_5608_);
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
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_del_object(v___x_5527_);
lean_dec(v_snd_5525_);
lean_dec(v_fst_5524_);
lean_del_object(v___x_5520_);
lean_dec_ref(v_snd_5503_);
lean_dec_ref(v_kp_5502_);
v_a_5615_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5530_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5530_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5626_, lean_object* v_snd_5627_, lean_object* v_stopAtFirstFailure_5628_, lean_object* v_as_x27_5629_, lean_object* v_b_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5641_; lean_object* v_res_5642_; 
v_stopAtFirstFailure_boxed_5641_ = lean_unbox(v_stopAtFirstFailure_5628_);
v_res_5642_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5626_, v_snd_5627_, v_stopAtFirstFailure_boxed_5641_, v_as_x27_5629_, v_b_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
lean_dec(v___y_5639_);
lean_dec_ref(v___y_5638_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec(v_as_x27_5629_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5643_, lean_object* v_c_5644_, lean_object* v___x_5645_, lean_object* v___x_5646_, uint8_t v_isRec_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_){
_start:
{
if (lean_obj_tag(v_a_5648_) == 0)
{
lean_object* v___x_5650_; 
lean_dec(v___x_5646_);
lean_dec_ref(v___x_5645_);
lean_dec_ref(v_snd_5643_);
v___x_5650_ = lean_array_to_list(v_a_5649_);
return v___x_5650_;
}
else
{
lean_object* v_toGoalState_5651_; lean_object* v_split_5652_; lean_object* v_head_5653_; lean_object* v_tail_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5714_; 
v_toGoalState_5651_ = lean_ctor_get(v_snd_5643_, 0);
lean_inc_ref(v_toGoalState_5651_);
v_split_5652_ = lean_ctor_get(v_toGoalState_5651_, 14);
lean_inc_ref(v_split_5652_);
v_head_5653_ = lean_ctor_get(v_a_5648_, 0);
v_tail_5654_ = lean_ctor_get(v_a_5648_, 1);
v_isSharedCheck_5714_ = !lean_is_exclusive(v_a_5648_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5656_ = v_a_5648_;
v_isShared_5657_ = v_isSharedCheck_5714_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_tail_5654_);
lean_inc(v_head_5653_);
lean_dec(v_a_5648_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5714_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v_nextDeclIdx_5658_; lean_object* v_enodeMap_5659_; lean_object* v_exprs_5660_; lean_object* v_parents_5661_; lean_object* v_congrTable_5662_; lean_object* v_appMap_5663_; lean_object* v_indicesFound_5664_; lean_object* v_toProcess_5665_; uint8_t v_inconsistent_5666_; lean_object* v_nextIdx_5667_; lean_object* v_newRawFacts_5668_; lean_object* v_facts_5669_; lean_object* v_extThms_5670_; lean_object* v_ematch_5671_; lean_object* v_inj_5672_; lean_object* v_clean_5673_; lean_object* v_sstates_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5712_; 
v_nextDeclIdx_5658_ = lean_ctor_get(v_toGoalState_5651_, 0);
v_enodeMap_5659_ = lean_ctor_get(v_toGoalState_5651_, 1);
v_exprs_5660_ = lean_ctor_get(v_toGoalState_5651_, 2);
v_parents_5661_ = lean_ctor_get(v_toGoalState_5651_, 3);
v_congrTable_5662_ = lean_ctor_get(v_toGoalState_5651_, 4);
v_appMap_5663_ = lean_ctor_get(v_toGoalState_5651_, 5);
v_indicesFound_5664_ = lean_ctor_get(v_toGoalState_5651_, 6);
v_toProcess_5665_ = lean_ctor_get(v_toGoalState_5651_, 7);
v_inconsistent_5666_ = lean_ctor_get_uint8(v_toGoalState_5651_, sizeof(void*)*17);
v_nextIdx_5667_ = lean_ctor_get(v_toGoalState_5651_, 8);
v_newRawFacts_5668_ = lean_ctor_get(v_toGoalState_5651_, 9);
v_facts_5669_ = lean_ctor_get(v_toGoalState_5651_, 10);
v_extThms_5670_ = lean_ctor_get(v_toGoalState_5651_, 11);
v_ematch_5671_ = lean_ctor_get(v_toGoalState_5651_, 12);
v_inj_5672_ = lean_ctor_get(v_toGoalState_5651_, 13);
v_clean_5673_ = lean_ctor_get(v_toGoalState_5651_, 15);
v_sstates_5674_ = lean_ctor_get(v_toGoalState_5651_, 16);
v_isSharedCheck_5712_ = !lean_is_exclusive(v_toGoalState_5651_);
if (v_isSharedCheck_5712_ == 0)
{
lean_object* v_unused_5713_; 
v_unused_5713_ = lean_ctor_get(v_toGoalState_5651_, 14);
lean_dec(v_unused_5713_);
v___x_5676_ = v_toGoalState_5651_;
v_isShared_5677_ = v_isSharedCheck_5712_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_sstates_5674_);
lean_inc(v_clean_5673_);
lean_inc(v_inj_5672_);
lean_inc(v_ematch_5671_);
lean_inc(v_extThms_5670_);
lean_inc(v_facts_5669_);
lean_inc(v_newRawFacts_5668_);
lean_inc(v_nextIdx_5667_);
lean_inc(v_toProcess_5665_);
lean_inc(v_indicesFound_5664_);
lean_inc(v_appMap_5663_);
lean_inc(v_congrTable_5662_);
lean_inc(v_parents_5661_);
lean_inc(v_exprs_5660_);
lean_inc(v_enodeMap_5659_);
lean_inc(v_nextDeclIdx_5658_);
lean_dec(v_toGoalState_5651_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5712_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v_num_5678_; lean_object* v_candidates_5679_; lean_object* v_added_5680_; lean_object* v_resolved_5681_; lean_object* v_trace_5682_; lean_object* v_lookaheads_5683_; lean_object* v_argPosMap_5684_; lean_object* v_argsAt_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5711_; 
v_num_5678_ = lean_ctor_get(v_split_5652_, 0);
v_candidates_5679_ = lean_ctor_get(v_split_5652_, 1);
v_added_5680_ = lean_ctor_get(v_split_5652_, 2);
v_resolved_5681_ = lean_ctor_get(v_split_5652_, 3);
v_trace_5682_ = lean_ctor_get(v_split_5652_, 4);
v_lookaheads_5683_ = lean_ctor_get(v_split_5652_, 5);
v_argPosMap_5684_ = lean_ctor_get(v_split_5652_, 6);
v_argsAt_5685_ = lean_ctor_get(v_split_5652_, 7);
v_isSharedCheck_5711_ = !lean_is_exclusive(v_split_5652_);
if (v_isSharedCheck_5711_ == 0)
{
v___x_5687_ = v_split_5652_;
v_isShared_5688_ = v_isSharedCheck_5711_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_argsAt_5685_);
lean_inc(v_argPosMap_5684_);
lean_inc(v_lookaheads_5683_);
lean_inc(v_trace_5682_);
lean_inc(v_resolved_5681_);
lean_inc(v_added_5680_);
lean_inc(v_candidates_5679_);
lean_inc(v_num_5678_);
lean_dec(v_split_5652_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5711_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5689_; lean_object* v___y_5691_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v___x_5689_ = lean_array_get_size(v_a_5649_);
v___x_5709_ = lean_unsigned_to_nat(0u);
v___x_5710_ = lean_nat_dec_lt(v___x_5709_, v___x_5689_);
if (v___x_5710_ == 0)
{
if (v_isRec_5647_ == 0)
{
v___y_5691_ = v_num_5678_;
goto v___jp_5690_;
}
else
{
goto v___jp_5706_;
}
}
else
{
goto v___jp_5706_;
}
v___jp_5690_:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5695_; 
v___x_5692_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5644_);
lean_inc(v___x_5646_);
lean_inc_ref(v___x_5645_);
v___x_5693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5645_);
lean_ctor_set(v___x_5693_, 1, v___x_5689_);
lean_ctor_set(v___x_5693_, 2, v___x_5646_);
lean_ctor_set(v___x_5693_, 3, v___x_5692_);
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 1, v_trace_5682_);
lean_ctor_set(v___x_5656_, 0, v___x_5693_);
v___x_5695_ = v___x_5656_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v___x_5693_);
lean_ctor_set(v_reuseFailAlloc_5705_, 1, v_trace_5682_);
v___x_5695_ = v_reuseFailAlloc_5705_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 4, v___x_5695_);
lean_ctor_set(v___x_5687_, 0, v___y_5691_);
v___x_5697_ = v___x_5687_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v___y_5691_);
lean_ctor_set(v_reuseFailAlloc_5704_, 1, v_candidates_5679_);
lean_ctor_set(v_reuseFailAlloc_5704_, 2, v_added_5680_);
lean_ctor_set(v_reuseFailAlloc_5704_, 3, v_resolved_5681_);
lean_ctor_set(v_reuseFailAlloc_5704_, 4, v___x_5695_);
lean_ctor_set(v_reuseFailAlloc_5704_, 5, v_lookaheads_5683_);
lean_ctor_set(v_reuseFailAlloc_5704_, 6, v_argPosMap_5684_);
lean_ctor_set(v_reuseFailAlloc_5704_, 7, v_argsAt_5685_);
v___x_5697_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5699_; 
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 14, v___x_5697_);
v___x_5699_ = v___x_5676_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_nextDeclIdx_5658_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v_enodeMap_5659_);
lean_ctor_set(v_reuseFailAlloc_5703_, 2, v_exprs_5660_);
lean_ctor_set(v_reuseFailAlloc_5703_, 3, v_parents_5661_);
lean_ctor_set(v_reuseFailAlloc_5703_, 4, v_congrTable_5662_);
lean_ctor_set(v_reuseFailAlloc_5703_, 5, v_appMap_5663_);
lean_ctor_set(v_reuseFailAlloc_5703_, 6, v_indicesFound_5664_);
lean_ctor_set(v_reuseFailAlloc_5703_, 7, v_toProcess_5665_);
lean_ctor_set(v_reuseFailAlloc_5703_, 8, v_nextIdx_5667_);
lean_ctor_set(v_reuseFailAlloc_5703_, 9, v_newRawFacts_5668_);
lean_ctor_set(v_reuseFailAlloc_5703_, 10, v_facts_5669_);
lean_ctor_set(v_reuseFailAlloc_5703_, 11, v_extThms_5670_);
lean_ctor_set(v_reuseFailAlloc_5703_, 12, v_ematch_5671_);
lean_ctor_set(v_reuseFailAlloc_5703_, 13, v_inj_5672_);
lean_ctor_set(v_reuseFailAlloc_5703_, 14, v___x_5697_);
lean_ctor_set(v_reuseFailAlloc_5703_, 15, v_clean_5673_);
lean_ctor_set(v_reuseFailAlloc_5703_, 16, v_sstates_5674_);
lean_ctor_set_uint8(v_reuseFailAlloc_5703_, sizeof(void*)*17, v_inconsistent_5666_);
v___x_5699_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
lean_object* v___x_5700_; lean_object* v___x_5701_; 
v___x_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set(v___x_5700_, 1, v_head_5653_);
v___x_5701_ = lean_array_push(v_a_5649_, v___x_5700_);
v_a_5648_ = v_tail_5654_;
v_a_5649_ = v___x_5701_;
goto _start;
}
}
}
}
v___jp_5706_:
{
lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___x_5707_ = lean_unsigned_to_nat(1u);
v___x_5708_ = lean_nat_add(v_num_5678_, v___x_5707_);
lean_dec(v_num_5678_);
v___y_5691_ = v___x_5708_;
goto v___jp_5690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5715_, lean_object* v_c_5716_, lean_object* v___x_5717_, lean_object* v___x_5718_, lean_object* v_isRec_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_){
_start:
{
uint8_t v_isRec_boxed_5722_; lean_object* v_res_5723_; 
v_isRec_boxed_5722_ = lean_unbox(v_isRec_5719_);
v_res_5723_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5715_, v_c_5716_, v___x_5717_, v___x_5718_, v_isRec_boxed_5722_, v_a_5720_, v_a_5721_);
lean_dec_ref(v_c_5716_);
return v_res_5723_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v___x_5735_ = lean_box(0);
v___x_5736_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5737_ = l_Lean_mkConst(v___x_5736_, v___x_5735_);
return v___x_5737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5738_, lean_object* v_numCases_5739_, uint8_t v_isRec_5740_, uint8_t v_stopAtFirstFailure_5741_, uint8_t v_compress_5742_, lean_object* v_candidates_x3f_5743_, lean_object* v_goal_5744_, lean_object* v_kp_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5747_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_object* v_a_5757_; uint8_t v_trace_5758_; lean_object* v___x_5759_; 
v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
lean_inc(v_a_5757_);
lean_dec_ref_known(v___x_5756_, 1);
v_trace_5758_ = lean_ctor_get_uint8(v_a_5757_, sizeof(void*)*14);
lean_dec(v_a_5757_);
lean_inc_ref(v_goal_5744_);
v___x_5759_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5744_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v_a_5760_; lean_object* v_mvarId_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___f_5764_; lean_object* v___x_5765_; lean_object* v___f_5766_; lean_object* v___x_5767_; 
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc_n(v_a_5760_, 2);
lean_dec_ref_known(v___x_5759_, 1);
v_mvarId_5761_ = lean_ctor_get(v_goal_5744_, 1);
lean_inc(v_mvarId_5761_);
v___x_5762_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5738_);
v___x_5763_ = lean_box(v_isRec_5740_);
lean_inc_ref_n(v_c_5738_, 2);
lean_inc_ref(v___x_5762_);
v___f_5764_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5764_, 0, v___x_5762_);
lean_closure_set(v___f_5764_, 1, v_c_5738_);
lean_closure_set(v___f_5764_, 2, v_a_5760_);
lean_closure_set(v___f_5764_, 3, v_numCases_5739_);
lean_closure_set(v___f_5764_, 4, v___x_5763_);
v___x_5765_ = lean_box(v_trace_5758_);
v___f_5766_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5766_, 0, v_goal_5744_);
lean_closure_set(v___f_5766_, 1, v___x_5765_);
lean_closure_set(v___f_5766_, 2, v___f_5764_);
lean_closure_set(v___f_5766_, 3, v_c_5738_);
lean_closure_set(v___f_5766_, 4, v_candidates_x3f_5743_);
v___x_5767_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5761_, v___f_5766_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_object* v_a_5768_; lean_object* v_fst_5769_; lean_object* v_snd_5770_; lean_object* v_fst_5771_; lean_object* v_snd_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; 
v_a_5768_ = lean_ctor_get(v___x_5767_, 0);
lean_inc(v_a_5768_);
lean_dec_ref_known(v___x_5767_, 1);
v_fst_5769_ = lean_ctor_get(v_a_5768_, 0);
lean_inc(v_fst_5769_);
v_snd_5770_ = lean_ctor_get(v_a_5768_, 1);
lean_inc_n(v_snd_5770_, 3);
lean_dec(v_a_5768_);
v_fst_5771_ = lean_ctor_get(v_fst_5769_, 0);
lean_inc(v_fst_5771_);
v_snd_5772_ = lean_ctor_get(v_fst_5769_, 1);
lean_inc(v_snd_5772_);
lean_dec(v_fst_5769_);
v___x_5773_ = l_List_lengthTR___redArg(v_fst_5771_);
v___x_5774_ = lean_unsigned_to_nat(0u);
v___x_5775_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5776_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5770_, v_c_5738_, v___x_5762_, v___x_5773_, v_isRec_5740_, v_fst_5771_, v___x_5775_);
lean_dec_ref(v_c_5738_);
v___x_5777_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5778_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5745_, v_snd_5770_, v_stopAtFirstFailure_5741_, v___x_5776_, v___x_5777_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_);
lean_dec(v___x_5776_);
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5862_; 
v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5862_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5862_ == 0)
{
v___x_5781_ = v___x_5778_;
v_isShared_5782_ = v_isSharedCheck_5862_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5778_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5862_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v_fst_5783_; 
v_fst_5783_ = lean_ctor_get(v_a_5779_, 0);
if (lean_obj_tag(v_fst_5783_) == 0)
{
lean_object* v_snd_5784_; lean_object* v_fst_5785_; lean_object* v_snd_5786_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v_mvarId_5836_; lean_object* v___x_5837_; 
v_snd_5784_ = lean_ctor_get(v_a_5779_, 1);
lean_inc(v_snd_5784_);
lean_dec(v_a_5779_);
v_fst_5785_ = lean_ctor_get(v_snd_5784_, 0);
lean_inc(v_fst_5785_);
v_snd_5786_ = lean_ctor_get(v_snd_5784_, 1);
lean_inc(v_snd_5786_);
lean_dec(v_snd_5784_);
v_mvarId_5836_ = lean_ctor_get(v_snd_5770_, 1);
lean_inc_n(v_mvarId_5836_, 2);
lean_dec(v_snd_5770_);
v___x_5837_ = l_Lean_MVarId_getType(v_mvarId_5836_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; uint8_t v___x_5839_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v___x_5837_, 1);
v___x_5839_ = l_Lean_Expr_isFalse(v_a_5838_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v_a_5842_; lean_object* v___x_5843_; 
v___x_5840_ = l_Lean_mkMVar(v_a_5760_);
v___x_5841_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5840_, v_a_5752_);
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5842_);
lean_dec_ref(v___x_5841_);
v___x_5843_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5836_, v_a_5842_, v_a_5752_);
lean_dec_ref(v___x_5843_);
v___y_5788_ = v_a_5753_;
v___y_5789_ = v_a_5754_;
goto v___jp_5787_;
}
else
{
lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v_a_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5844_ = l_Lean_mkMVar(v_a_5760_);
v___x_5845_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5844_, v_a_5752_);
v_a_5846_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_a_5846_);
lean_dec_ref(v___x_5845_);
v___x_5847_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5848_ = l_Lean_Meta_mkExpectedPropHint(v_a_5846_, v___x_5847_);
v___x_5849_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5836_, v___x_5848_, v_a_5752_);
lean_dec_ref(v___x_5849_);
v___y_5788_ = v_a_5753_;
v___y_5789_ = v_a_5754_;
goto v___jp_5787_;
}
}
else
{
lean_object* v_a_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5857_; 
lean_dec(v_mvarId_5836_);
lean_dec(v_snd_5786_);
lean_dec(v_fst_5785_);
lean_del_object(v___x_5781_);
lean_dec(v_snd_5772_);
lean_dec(v_a_5760_);
v_a_5850_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5857_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5852_ = v___x_5837_;
v_isShared_5853_ = v_isSharedCheck_5857_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_a_5850_);
lean_dec(v___x_5837_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5857_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v___x_5855_; 
if (v_isShared_5853_ == 0)
{
v___x_5855_ = v___x_5852_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_a_5850_);
v___x_5855_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
return v___x_5855_;
}
}
}
v___jp_5787_:
{
lean_object* v___x_5790_; uint8_t v___x_5791_; 
v___x_5790_ = lean_array_get_size(v_snd_5786_);
v___x_5791_ = lean_nat_dec_eq(v___x_5790_, v___x_5774_);
if (v___x_5791_ == 0)
{
lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5795_; 
lean_dec(v_fst_5785_);
lean_dec(v_snd_5772_);
v___x_5792_ = lean_array_to_list(v_snd_5786_);
v___x_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5792_);
if (v_isShared_5782_ == 0)
{
lean_ctor_set(v___x_5781_, 0, v___x_5793_);
v___x_5795_ = v___x_5781_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5793_);
v___x_5795_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
return v___x_5795_;
}
}
else
{
lean_dec(v_snd_5786_);
if (lean_obj_tag(v_snd_5772_) == 1)
{
lean_object* v_val_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5831_; 
lean_del_object(v___x_5781_);
v_val_5797_ = lean_ctor_get(v_snd_5772_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_snd_5772_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5799_ = v_snd_5772_;
v_isShared_5800_ = v_isSharedCheck_5831_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_val_5797_);
lean_dec(v_snd_5772_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5831_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5801_; 
v___x_5801_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5797_, v___y_5788_);
lean_dec(v_val_5797_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; lean_object* v___x_5803_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
lean_inc(v_a_5802_);
lean_dec_ref_known(v___x_5801_, 1);
v___x_5803_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5802_, v_fst_5785_, v_compress_5742_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5814_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5806_ = v___x_5803_;
v_isShared_5807_ = v_isSharedCheck_5814_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_a_5804_);
lean_dec(v___x_5803_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5814_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v___x_5809_; 
if (v_isShared_5800_ == 0)
{
lean_ctor_set_tag(v___x_5799_, 0);
lean_ctor_set(v___x_5799_, 0, v_a_5804_);
v___x_5809_ = v___x_5799_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_a_5804_);
v___x_5809_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
lean_object* v___x_5811_; 
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 0, v___x_5809_);
v___x_5811_ = v___x_5806_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5809_);
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
lean_object* v_a_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5822_; 
lean_del_object(v___x_5799_);
v_a_5815_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5817_ = v___x_5803_;
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_a_5815_);
lean_dec(v___x_5803_);
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
lean_del_object(v___x_5799_);
lean_dec(v_fst_5785_);
v_a_5823_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5825_ = v___x_5801_;
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5801_);
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
else
{
lean_object* v___x_5832_; lean_object* v___x_5834_; 
lean_dec(v_fst_5785_);
lean_dec(v_snd_5772_);
v___x_5832_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5782_ == 0)
{
lean_ctor_set(v___x_5781_, 0, v___x_5832_);
v___x_5834_ = v___x_5781_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v___x_5832_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
}
}
else
{
lean_object* v_val_5858_; lean_object* v___x_5860_; 
lean_inc_ref(v_fst_5783_);
lean_dec(v_a_5779_);
lean_dec(v_snd_5772_);
lean_dec(v_snd_5770_);
lean_dec(v_a_5760_);
v_val_5858_ = lean_ctor_get(v_fst_5783_, 0);
lean_inc(v_val_5858_);
lean_dec_ref_known(v_fst_5783_, 1);
if (v_isShared_5782_ == 0)
{
lean_ctor_set(v___x_5781_, 0, v_val_5858_);
v___x_5860_ = v___x_5781_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_val_5858_);
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
else
{
lean_object* v_a_5863_; lean_object* v___x_5865_; uint8_t v_isShared_5866_; uint8_t v_isSharedCheck_5870_; 
lean_dec(v_snd_5772_);
lean_dec(v_snd_5770_);
lean_dec(v_a_5760_);
v_a_5863_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5865_ = v___x_5778_;
v_isShared_5866_ = v_isSharedCheck_5870_;
goto v_resetjp_5864_;
}
else
{
lean_inc(v_a_5863_);
lean_dec(v___x_5778_);
v___x_5865_ = lean_box(0);
v_isShared_5866_ = v_isSharedCheck_5870_;
goto v_resetjp_5864_;
}
v_resetjp_5864_:
{
lean_object* v___x_5868_; 
if (v_isShared_5866_ == 0)
{
v___x_5868_ = v___x_5865_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
v___x_5868_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
return v___x_5868_;
}
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v___x_5762_);
lean_dec(v_a_5760_);
lean_dec_ref(v_kp_5745_);
lean_dec_ref(v_c_5738_);
v_a_5871_ = lean_ctor_get(v___x_5767_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5767_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5767_);
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
else
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5886_; 
lean_dec_ref(v_kp_5745_);
lean_dec_ref(v_goal_5744_);
lean_dec(v_candidates_x3f_5743_);
lean_dec(v_numCases_5739_);
lean_dec_ref(v_c_5738_);
v_a_5879_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5881_ = v___x_5759_;
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5759_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5884_; 
if (v_isShared_5882_ == 0)
{
v___x_5884_ = v___x_5881_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5894_; 
lean_dec_ref(v_kp_5745_);
lean_dec_ref(v_goal_5744_);
lean_dec(v_candidates_x3f_5743_);
lean_dec(v_numCases_5739_);
lean_dec_ref(v_c_5738_);
v_a_5887_ = lean_ctor_get(v___x_5756_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5756_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5889_ = v___x_5756_;
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5756_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5892_; 
if (v_isShared_5890_ == 0)
{
v___x_5892_ = v___x_5889_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_a_5887_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5895_ = _args[0];
lean_object* v_numCases_5896_ = _args[1];
lean_object* v_isRec_5897_ = _args[2];
lean_object* v_stopAtFirstFailure_5898_ = _args[3];
lean_object* v_compress_5899_ = _args[4];
lean_object* v_candidates_x3f_5900_ = _args[5];
lean_object* v_goal_5901_ = _args[6];
lean_object* v_kp_5902_ = _args[7];
lean_object* v_a_5903_ = _args[8];
lean_object* v_a_5904_ = _args[9];
lean_object* v_a_5905_ = _args[10];
lean_object* v_a_5906_ = _args[11];
lean_object* v_a_5907_ = _args[12];
lean_object* v_a_5908_ = _args[13];
lean_object* v_a_5909_ = _args[14];
lean_object* v_a_5910_ = _args[15];
lean_object* v_a_5911_ = _args[16];
lean_object* v_a_5912_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5913_; uint8_t v_stopAtFirstFailure_boxed_5914_; uint8_t v_compress_boxed_5915_; lean_object* v_res_5916_; 
v_isRec_boxed_5913_ = lean_unbox(v_isRec_5897_);
v_stopAtFirstFailure_boxed_5914_ = lean_unbox(v_stopAtFirstFailure_5898_);
v_compress_boxed_5915_ = lean_unbox(v_compress_5899_);
v_res_5916_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5895_, v_numCases_5896_, v_isRec_boxed_5913_, v_stopAtFirstFailure_boxed_5914_, v_compress_boxed_5915_, v_candidates_x3f_5900_, v_goal_5901_, v_kp_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_, v_a_5907_, v_a_5908_, v_a_5909_, v_a_5910_, v_a_5911_);
lean_dec(v_a_5911_);
lean_dec_ref(v_a_5910_);
lean_dec(v_a_5909_);
lean_dec_ref(v_a_5908_);
lean_dec(v_a_5907_);
lean_dec_ref(v_a_5906_);
lean_dec(v_a_5905_);
lean_dec_ref(v_a_5904_);
lean_dec(v_a_5903_);
return v_res_5916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5917_, lean_object* v_numCases_5918_, uint8_t v_isRec_5919_, uint8_t v_stopAtFirstFailure_5920_, uint8_t v_compress_5921_, lean_object* v_candidates_x3f_5922_, lean_object* v_goal_5923_, lean_object* v_x_5924_, lean_object* v_kp_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_){
_start:
{
lean_object* v___x_5936_; 
v___x_5936_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5917_, v_numCases_5918_, v_isRec_5919_, v_stopAtFirstFailure_5920_, v_compress_5921_, v_candidates_x3f_5922_, v_goal_5923_, v_kp_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_);
return v___x_5936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5937_ = _args[0];
lean_object* v_numCases_5938_ = _args[1];
lean_object* v_isRec_5939_ = _args[2];
lean_object* v_stopAtFirstFailure_5940_ = _args[3];
lean_object* v_compress_5941_ = _args[4];
lean_object* v_candidates_x3f_5942_ = _args[5];
lean_object* v_goal_5943_ = _args[6];
lean_object* v_x_5944_ = _args[7];
lean_object* v_kp_5945_ = _args[8];
lean_object* v_a_5946_ = _args[9];
lean_object* v_a_5947_ = _args[10];
lean_object* v_a_5948_ = _args[11];
lean_object* v_a_5949_ = _args[12];
lean_object* v_a_5950_ = _args[13];
lean_object* v_a_5951_ = _args[14];
lean_object* v_a_5952_ = _args[15];
lean_object* v_a_5953_ = _args[16];
lean_object* v_a_5954_ = _args[17];
lean_object* v_a_5955_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5956_; uint8_t v_stopAtFirstFailure_boxed_5957_; uint8_t v_compress_boxed_5958_; lean_object* v_res_5959_; 
v_isRec_boxed_5956_ = lean_unbox(v_isRec_5939_);
v_stopAtFirstFailure_boxed_5957_ = lean_unbox(v_stopAtFirstFailure_5940_);
v_compress_boxed_5958_ = lean_unbox(v_compress_5941_);
v_res_5959_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5937_, v_numCases_5938_, v_isRec_boxed_5956_, v_stopAtFirstFailure_boxed_5957_, v_compress_boxed_5958_, v_candidates_x3f_5942_, v_goal_5943_, v_x_5944_, v_kp_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_);
lean_dec(v_a_5954_);
lean_dec_ref(v_a_5953_);
lean_dec(v_a_5952_);
lean_dec_ref(v_a_5951_);
lean_dec(v_a_5950_);
lean_dec_ref(v_a_5949_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec_ref(v_x_5944_);
return v_res_5959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5960_, lean_object* v_snd_5961_, uint8_t v_stopAtFirstFailure_5962_, lean_object* v_as_5963_, lean_object* v_as_x27_5964_, lean_object* v_b_5965_, lean_object* v_a_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5960_, v_snd_5961_, v_stopAtFirstFailure_5962_, v_as_x27_5964_, v_b_5965_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5978_ = _args[0];
lean_object* v_snd_5979_ = _args[1];
lean_object* v_stopAtFirstFailure_5980_ = _args[2];
lean_object* v_as_5981_ = _args[3];
lean_object* v_as_x27_5982_ = _args[4];
lean_object* v_b_5983_ = _args[5];
lean_object* v_a_5984_ = _args[6];
lean_object* v___y_5985_ = _args[7];
lean_object* v___y_5986_ = _args[8];
lean_object* v___y_5987_ = _args[9];
lean_object* v___y_5988_ = _args[10];
lean_object* v___y_5989_ = _args[11];
lean_object* v___y_5990_ = _args[12];
lean_object* v___y_5991_ = _args[13];
lean_object* v___y_5992_ = _args[14];
lean_object* v___y_5993_ = _args[15];
lean_object* v___y_5994_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5995_; lean_object* v_res_5996_; 
v_stopAtFirstFailure_boxed_5995_ = lean_unbox(v_stopAtFirstFailure_5980_);
v_res_5996_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5978_, v_snd_5979_, v_stopAtFirstFailure_boxed_5995_, v_as_5981_, v_as_x27_5982_, v_b_5983_, v_a_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
lean_dec(v___y_5993_);
lean_dec_ref(v___y_5992_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
lean_dec(v___y_5987_);
lean_dec_ref(v___y_5986_);
lean_dec(v___y_5985_);
lean_dec(v_as_x27_5982_);
lean_dec(v_as_5981_);
return v_res_5996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_5997_, lean_object* v_val_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_){
_start:
{
lean_object* v___x_6009_; 
v___x_6009_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5997_, v_val_5998_, v___y_6005_);
return v___x_6009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6010_, lean_object* v_val_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v_res_6022_; 
v_res_6022_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6010_, v_val_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec(v___y_6018_);
lean_dec_ref(v___y_6017_);
lean_dec(v___y_6016_);
lean_dec_ref(v___y_6015_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec(v___y_6012_);
return v_res_6022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6023_, lean_object* v_x_6024_, lean_object* v_x_6025_, lean_object* v_x_6026_){
_start:
{
lean_object* v___x_6027_; 
v___x_6027_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6024_, v_x_6025_, v_x_6026_);
return v___x_6027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6028_, lean_object* v_x_6029_, size_t v_x_6030_, size_t v_x_6031_, lean_object* v_x_6032_, lean_object* v_x_6033_){
_start:
{
lean_object* v___x_6034_; 
v___x_6034_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6029_, v_x_6030_, v_x_6031_, v_x_6032_, v_x_6033_);
return v___x_6034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6035_, lean_object* v_x_6036_, lean_object* v_x_6037_, lean_object* v_x_6038_, lean_object* v_x_6039_, lean_object* v_x_6040_){
_start:
{
size_t v_x_67873__boxed_6041_; size_t v_x_67874__boxed_6042_; lean_object* v_res_6043_; 
v_x_67873__boxed_6041_ = lean_unbox_usize(v_x_6037_);
lean_dec(v_x_6037_);
v_x_67874__boxed_6042_ = lean_unbox_usize(v_x_6038_);
lean_dec(v_x_6038_);
v_res_6043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6035_, v_x_6036_, v_x_67873__boxed_6041_, v_x_67874__boxed_6042_, v_x_6039_, v_x_6040_);
return v_res_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6044_, lean_object* v_n_6045_, lean_object* v_k_6046_, lean_object* v_v_6047_){
_start:
{
lean_object* v___x_6048_; 
v___x_6048_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6045_, v_k_6046_, v_v_6047_);
return v___x_6048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6049_, size_t v_depth_6050_, lean_object* v_keys_6051_, lean_object* v_vals_6052_, lean_object* v_heq_6053_, lean_object* v_i_6054_, lean_object* v_entries_6055_){
_start:
{
lean_object* v___x_6056_; 
v___x_6056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6050_, v_keys_6051_, v_vals_6052_, v_i_6054_, v_entries_6055_);
return v___x_6056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6057_, lean_object* v_depth_6058_, lean_object* v_keys_6059_, lean_object* v_vals_6060_, lean_object* v_heq_6061_, lean_object* v_i_6062_, lean_object* v_entries_6063_){
_start:
{
size_t v_depth_boxed_6064_; lean_object* v_res_6065_; 
v_depth_boxed_6064_ = lean_unbox_usize(v_depth_6058_);
lean_dec(v_depth_6058_);
v_res_6065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6057_, v_depth_boxed_6064_, v_keys_6059_, v_vals_6060_, v_heq_6061_, v_i_6062_, v_entries_6063_);
lean_dec_ref(v_vals_6060_);
lean_dec_ref(v_keys_6059_);
return v_res_6065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6066_, lean_object* v_x_6067_, lean_object* v_x_6068_, lean_object* v_x_6069_, lean_object* v_x_6070_){
_start:
{
lean_object* v___x_6071_; 
v___x_6071_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6067_, v_x_6068_, v_x_6069_, v_x_6070_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_){
_start:
{
lean_object* v___x_6085_; 
v___x_6085_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6072_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_){
_start:
{
lean_object* v_res_6099_; 
v_res_6099_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_);
lean_dec(v___y_6097_);
lean_dec_ref(v___y_6096_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
lean_dec(v___y_6089_);
lean_dec_ref(v___y_6087_);
return v_res_6099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; 
v___x_6111_ = lean_st_mk_ref(v_goal_6100_);
v___x_6112_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6111_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_);
if (lean_obj_tag(v___x_6112_) == 0)
{
lean_object* v_a_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6122_; 
v_a_6113_ = lean_ctor_get(v___x_6112_, 0);
v_isSharedCheck_6122_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6122_ == 0)
{
v___x_6115_ = v___x_6112_;
v_isShared_6116_ = v_isSharedCheck_6122_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_a_6113_);
lean_dec(v___x_6112_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6122_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6120_; 
v___x_6117_ = lean_st_ref_get(v___x_6111_);
lean_dec(v___x_6111_);
v___x_6118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6118_, 0, v_a_6113_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
if (v_isShared_6116_ == 0)
{
lean_ctor_set(v___x_6115_, 0, v___x_6118_);
v___x_6120_ = v___x_6115_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6118_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
else
{
lean_object* v_a_6123_; lean_object* v___x_6125_; uint8_t v_isShared_6126_; uint8_t v_isSharedCheck_6130_; 
lean_dec(v___x_6111_);
v_a_6123_ = lean_ctor_get(v___x_6112_, 0);
v_isSharedCheck_6130_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6130_ == 0)
{
v___x_6125_ = v___x_6112_;
v_isShared_6126_ = v_isSharedCheck_6130_;
goto v_resetjp_6124_;
}
else
{
lean_inc(v_a_6123_);
lean_dec(v___x_6112_);
v___x_6125_ = lean_box(0);
v_isShared_6126_ = v_isSharedCheck_6130_;
goto v_resetjp_6124_;
}
v_resetjp_6124_:
{
lean_object* v___x_6128_; 
if (v_isShared_6126_ == 0)
{
v___x_6128_ = v___x_6125_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v_a_6123_);
v___x_6128_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
return v___x_6128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_){
_start:
{
lean_object* v_res_6142_; 
v_res_6142_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v___y_6134_);
lean_dec_ref(v___y_6133_);
lean_dec(v___y_6132_);
return v_res_6142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6143_, lean_object* v___f_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6158_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6158_, 0, v___y_6143_);
v___x_6159_ = l_Lean_Meta_Grind_Action_andThen(v___x_6158_, v___f_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6160_, lean_object* v___f_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_){
_start:
{
lean_object* v_res_6175_; 
v_res_6175_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6160_, v___f_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec(v___y_6169_);
lean_dec_ref(v___y_6168_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
lean_dec(v___y_6165_);
return v_res_6175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6177_, uint8_t v_compress_6178_, lean_object* v_goal_6179_, lean_object* v_kna_6180_, lean_object* v_kp_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_){
_start:
{
lean_object* v_toGoalState_6192_; lean_object* v_split_6193_; lean_object* v_mvarId_6194_; lean_object* v_candidates_6195_; lean_object* v___f_6196_; lean_object* v___f_6197_; lean_object* v___x_6198_; 
v_toGoalState_6192_ = lean_ctor_get(v_goal_6179_, 0);
v_split_6193_ = lean_ctor_get(v_toGoalState_6192_, 14);
v_mvarId_6194_ = lean_ctor_get(v_goal_6179_, 1);
lean_inc(v_mvarId_6194_);
v_candidates_6195_ = lean_ctor_get(v_split_6193_, 1);
lean_inc(v_candidates_6195_);
v___f_6196_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6197_, 0, v_goal_6179_);
v___x_6198_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6194_, v___f_6197_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_);
if (lean_obj_tag(v___x_6198_) == 0)
{
lean_object* v_a_6199_; lean_object* v_fst_6200_; 
v_a_6199_ = lean_ctor_get(v___x_6198_, 0);
lean_inc(v_a_6199_);
lean_dec_ref_known(v___x_6198_, 1);
v_fst_6200_ = lean_ctor_get(v_a_6199_, 0);
if (lean_obj_tag(v_fst_6200_) == 1)
{
lean_object* v_snd_6201_; lean_object* v_c_6202_; lean_object* v_numCases_6203_; uint8_t v_isRec_6204_; lean_object* v___y_6206_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; uint8_t v___x_6219_; 
lean_inc_ref(v_fst_6200_);
v_snd_6201_ = lean_ctor_get(v_a_6199_, 1);
lean_inc(v_snd_6201_);
lean_dec(v_a_6199_);
v_c_6202_ = lean_ctor_get(v_fst_6200_, 0);
lean_inc_ref(v_c_6202_);
v_numCases_6203_ = lean_ctor_get(v_fst_6200_, 1);
lean_inc(v_numCases_6203_);
v_isRec_6204_ = lean_ctor_get_uint8(v_fst_6200_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6200_, 2);
v___x_6214_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6202_);
v___x_6215_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6201_, v___x_6214_);
lean_dec_ref(v___x_6214_);
v___x_6216_ = lean_unsigned_to_nat(1u);
v___x_6219_ = lean_nat_dec_lt(v___x_6216_, v_numCases_6203_);
if (v___x_6219_ == 0)
{
if (v_isRec_6204_ == 0)
{
v___y_6206_ = v___x_6215_;
goto v___jp_6205_;
}
else
{
goto v___jp_6217_;
}
}
else
{
goto v___jp_6217_;
}
v___jp_6205_:
{
lean_object* v___f_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___f_6207_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6207_, 0, v___y_6206_);
lean_closure_set(v___f_6207_, 1, v___f_6196_);
v___x_6208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6208_, 0, v_candidates_6195_);
v___x_6209_ = lean_box(v_isRec_6204_);
v___x_6210_ = lean_box(v_stopAtFirstFailure_6177_);
v___x_6211_ = lean_box(v_compress_6178_);
v___x_6212_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6212_, 0, v_c_6202_);
lean_closure_set(v___x_6212_, 1, v_numCases_6203_);
lean_closure_set(v___x_6212_, 2, v___x_6209_);
lean_closure_set(v___x_6212_, 3, v___x_6210_);
lean_closure_set(v___x_6212_, 4, v___x_6211_);
lean_closure_set(v___x_6212_, 5, v___x_6208_);
v___x_6213_ = l_Lean_Meta_Grind_Action_andThen(v___x_6212_, v___f_6207_, v_snd_6201_, v_kna_6180_, v_kp_6181_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_);
return v___x_6213_;
}
v___jp_6217_:
{
lean_object* v___x_6218_; 
v___x_6218_ = lean_nat_add(v___x_6215_, v___x_6216_);
lean_dec(v___x_6215_);
v___y_6206_ = v___x_6218_;
goto v___jp_6205_;
}
}
else
{
lean_object* v_snd_6220_; lean_object* v___x_6221_; 
lean_dec(v_candidates_6195_);
lean_dec_ref(v_kp_6181_);
v_snd_6220_ = lean_ctor_get(v_a_6199_, 1);
lean_inc(v_snd_6220_);
lean_dec(v_a_6199_);
lean_inc(v_a_6190_);
lean_inc_ref(v_a_6189_);
lean_inc(v_a_6188_);
lean_inc_ref(v_a_6187_);
lean_inc(v_a_6186_);
lean_inc_ref(v_a_6185_);
lean_inc(v_a_6184_);
lean_inc_ref(v_a_6183_);
lean_inc(v_a_6182_);
v___x_6221_ = lean_apply_11(v_kna_6180_, v_snd_6220_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_, lean_box(0));
return v___x_6221_;
}
}
else
{
lean_object* v_a_6222_; lean_object* v___x_6224_; uint8_t v_isShared_6225_; uint8_t v_isSharedCheck_6229_; 
lean_dec(v_candidates_6195_);
lean_dec_ref(v_kp_6181_);
lean_dec_ref(v_kna_6180_);
v_a_6222_ = lean_ctor_get(v___x_6198_, 0);
v_isSharedCheck_6229_ = !lean_is_exclusive(v___x_6198_);
if (v_isSharedCheck_6229_ == 0)
{
v___x_6224_ = v___x_6198_;
v_isShared_6225_ = v_isSharedCheck_6229_;
goto v_resetjp_6223_;
}
else
{
lean_inc(v_a_6222_);
lean_dec(v___x_6198_);
v___x_6224_ = lean_box(0);
v_isShared_6225_ = v_isSharedCheck_6229_;
goto v_resetjp_6223_;
}
v_resetjp_6223_:
{
lean_object* v___x_6227_; 
if (v_isShared_6225_ == 0)
{
v___x_6227_ = v___x_6224_;
goto v_reusejp_6226_;
}
else
{
lean_object* v_reuseFailAlloc_6228_; 
v_reuseFailAlloc_6228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_a_6222_);
v___x_6227_ = v_reuseFailAlloc_6228_;
goto v_reusejp_6226_;
}
v_reusejp_6226_:
{
return v___x_6227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6230_, lean_object* v_compress_6231_, lean_object* v_goal_6232_, lean_object* v_kna_6233_, lean_object* v_kp_6234_, lean_object* v_a_6235_, lean_object* v_a_6236_, lean_object* v_a_6237_, lean_object* v_a_6238_, lean_object* v_a_6239_, lean_object* v_a_6240_, lean_object* v_a_6241_, lean_object* v_a_6242_, lean_object* v_a_6243_, lean_object* v_a_6244_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6245_; uint8_t v_compress_boxed_6246_; lean_object* v_res_6247_; 
v_stopAtFirstFailure_boxed_6245_ = lean_unbox(v_stopAtFirstFailure_6230_);
v_compress_boxed_6246_ = lean_unbox(v_compress_6231_);
v_res_6247_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6245_, v_compress_boxed_6246_, v_goal_6232_, v_kna_6233_, v_kp_6234_, v_a_6235_, v_a_6236_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_, v_a_6241_, v_a_6242_, v_a_6243_);
lean_dec(v_a_6243_);
lean_dec_ref(v_a_6242_);
lean_dec(v_a_6241_);
lean_dec_ref(v_a_6240_);
lean_dec(v_a_6239_);
lean_dec_ref(v_a_6238_);
lean_dec(v_a_6237_);
lean_dec_ref(v_a_6236_);
lean_dec(v_a_6235_);
return v_res_6247_;
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
