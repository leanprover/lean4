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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Meta_Grind_Goal_isCongruent(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_casesMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_source(lean_object*);
lean_object* l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getGeneration(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "split resolved: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 59, 213, 47, 128, 196, 59, 0)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "may be irrelevant\na: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nb: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\neq: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\narg_a: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\narg_b: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", gen: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 96, 222, 221, 183, 249, 85, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", generation: "};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2;
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
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 158, 17, 45, 135, 214, 137)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_ref_"};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(236, 234, 46, 225, 9, 69, 165, 154)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_splitNext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_splitNext___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitNext___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Meta_Grind_SplitStatus_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
lean_object* v_numCases_9_; uint8_t v_isRec_10_; uint8_t v_tryPostpone_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_numCases_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_numCases_9_);
v_isRec_10_ = lean_ctor_get_uint8(v_t_7_, sizeof(void*)*1);
v_tryPostpone_11_ = lean_ctor_get_uint8(v_t_7_, sizeof(void*)*1 + 1);
lean_dec_ref(v_t_7_);
v___x_12_ = lean_box(v_isRec_10_);
v___x_13_ = lean_box(v_tryPostpone_11_);
v___x_14_ = lean_apply_3(v_k_8_, v_numCases_9_, v___x_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Grind_SplitStatus_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim___redArg(lean_object* v_t_27_, lean_object* v_resolved_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_27_, v_resolved_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_resolved_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_31_, v_resolved_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim___redArg(lean_object* v_t_35_, lean_object* v_notReady_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_35_, v_notReady_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_notReady_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_39_, v_notReady_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim___redArg(lean_object* v_t_43_, lean_object* v_ready_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_43_, v_ready_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_ready_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(v_t_47_, v_ready_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus_default(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqSplitStatus_beq(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
switch(lean_obj_tag(v_x_53_))
{
case 0:
{
if (lean_obj_tag(v_x_54_) == 0)
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
case 1:
{
if (lean_obj_tag(v_x_54_) == 1)
{
uint8_t v___x_57_; 
v___x_57_ = 1;
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = 0;
return v___x_58_;
}
}
default: 
{
if (lean_obj_tag(v_x_54_) == 2)
{
lean_object* v_numCases_59_; uint8_t v_isRec_60_; uint8_t v_tryPostpone_61_; lean_object* v_numCases_62_; uint8_t v_isRec_63_; uint8_t v_tryPostpone_64_; uint8_t v___y_66_; uint8_t v___x_67_; 
v_numCases_59_ = lean_ctor_get(v_x_53_, 0);
v_isRec_60_ = lean_ctor_get_uint8(v_x_53_, sizeof(void*)*1);
v_tryPostpone_61_ = lean_ctor_get_uint8(v_x_53_, sizeof(void*)*1 + 1);
v_numCases_62_ = lean_ctor_get(v_x_54_, 0);
v_isRec_63_ = lean_ctor_get_uint8(v_x_54_, sizeof(void*)*1);
v_tryPostpone_64_ = lean_ctor_get_uint8(v_x_54_, sizeof(void*)*1 + 1);
v___x_67_ = lean_nat_dec_eq(v_numCases_59_, v_numCases_62_);
if (v___x_67_ == 0)
{
return v___x_67_;
}
else
{
if (v_isRec_60_ == 0)
{
if (v_isRec_63_ == 0)
{
v___y_66_ = v___x_67_;
goto v___jp_65_;
}
else
{
return v_isRec_60_;
}
}
else
{
v___y_66_ = v_isRec_63_;
goto v___jp_65_;
}
}
v___jp_65_:
{
if (v___y_66_ == 0)
{
return v___y_66_;
}
else
{
if (v_tryPostpone_61_ == 0)
{
if (v_tryPostpone_64_ == 0)
{
return v___y_66_;
}
else
{
return v_tryPostpone_61_;
}
}
else
{
return v_tryPostpone_64_;
}
}
}
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Meta_Grind_instBEqSplitStatus_beq(v_x_69_, v_x_70_);
lean_dec(v_x_70_);
lean_dec(v_x_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(2u);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr(lean_object* v_x_91_, lean_object* v_prec_92_){
_start:
{
lean_object* v___y_94_; lean_object* v___y_101_; 
switch(lean_obj_tag(v_x_91_))
{
case 0:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_92_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_101_ = v___x_109_;
goto v___jp_100_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_101_ = v___x_110_;
goto v___jp_100_;
}
}
case 1:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1024u);
v___x_112_ = lean_nat_dec_le(v___x_111_, v_prec_92_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_94_ = v___x_113_;
goto v___jp_93_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_94_ = v___x_114_;
goto v___jp_93_;
}
}
default: 
{
lean_object* v_numCases_115_; uint8_t v_isRec_116_; uint8_t v_tryPostpone_117_; lean_object* v___y_119_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_numCases_115_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_numCases_115_);
v_isRec_116_ = lean_ctor_get_uint8(v_x_91_, sizeof(void*)*1);
v_tryPostpone_117_ = lean_ctor_get_uint8(v_x_91_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_91_);
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_prec_92_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_119_ = v___x_137_;
goto v___jp_118_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_119_ = v___x_138_;
goto v___jp_118_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_120_ = lean_box(1);
v___x_121_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8));
v___x_122_ = l_Nat_reprFast(v_numCases_115_);
v___x_123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_121_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_120_);
v___x_126_ = l_Bool_repr___redArg(v_isRec_116_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_120_);
v___x_129_ = l_Bool_repr___redArg(v_tryPostpone_117_);
v___x_130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_131_, 0, v___y_119_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = 0;
v___x_133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_132_);
v___x_134_ = l_Repr_addAppParen(v___x_133_, v_prec_92_);
return v___x_134_;
}
}
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1));
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_92_);
return v___x_99_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_102_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3));
v___x_103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_103_, 0, v___y_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = 0;
v___x_105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_104_);
v___x_106_ = l_Repr_addAppParen(v___x_105_, v_prec_92_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed(lean_object* v_x_139_, lean_object* v_prec_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_instReprSplitStatus_repr(v_x_139_, v_prec_140_);
lean_dec(v_prec_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object* v_c_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___y_153_; lean_object* v___x_179_; 
lean_inc_ref(v_c_144_);
v___x_179_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; uint8_t v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
v___x_181_ = lean_unbox(v_a_180_);
lean_dec(v_a_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v___x_179_);
v___x_182_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
v___y_153_ = v___x_182_;
goto v___jp_152_;
}
else
{
lean_dec_ref(v_c_144_);
v___y_153_ = v___x_179_;
goto v___jp_152_;
}
}
else
{
lean_dec_ref(v_c_144_);
v___y_153_ = v___x_179_;
goto v___jp_152_;
}
v___jp_152_:
{
if (lean_obj_tag(v___y_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_170_; 
v_a_154_ = lean_ctor_get(v___y_153_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___y_153_);
if (v_isSharedCheck_170_ == 0)
{
v___x_156_ = v___y_153_;
v_isShared_157_ = v_isSharedCheck_170_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___y_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_170_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint8_t v___x_158_; 
v___x_158_ = lean_unbox(v_a_154_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; uint8_t v___x_162_; lean_object* v___x_164_; 
v___x_159_ = lean_unsigned_to_nat(2u);
v___x_160_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = lean_unbox(v_a_154_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_161_);
v___x_162_ = lean_unbox(v_a_154_);
lean_dec(v_a_154_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1 + 1, v___x_162_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_160_);
v___x_164_ = v___x_156_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_160_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_a_154_);
v___x_166_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_166_);
v___x_168_ = v___x_156_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___y_153_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___y_153_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___y_153_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___y_153_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object* v_c_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* v_c_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_192_, v_a_193_, v_a_197_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* v_c_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(v_c_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec(v_a_206_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* v_e_218_, lean_object* v_a_219_, lean_object* v_b_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___y_229_; lean_object* v___x_255_; 
lean_inc_ref(v_e_218_);
v___x_255_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_218_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_255_);
v___x_257_ = lean_unbox(v_a_256_);
lean_dec(v_a_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_b_220_);
lean_dec_ref(v_a_219_);
v___x_258_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_218_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_272_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_272_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; 
v___x_263_ = lean_unbox(v_a_259_);
lean_dec(v_a_259_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_box(1);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_268_);
v___x_270_ = v___x_261_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_258_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_258_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v___x_281_; 
lean_dec_ref(v_e_218_);
v___x_281_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_219_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; uint8_t v___x_283_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
v___x_283_ = lean_unbox(v_a_282_);
lean_dec(v_a_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec_ref(v___x_281_);
v___x_284_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
v___y_229_ = v___x_284_;
goto v___jp_228_;
}
else
{
lean_dec_ref(v_b_220_);
v___y_229_ = v___x_281_;
goto v___jp_228_;
}
}
else
{
lean_dec_ref(v_b_220_);
v___y_229_ = v___x_281_;
goto v___jp_228_;
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_b_220_);
lean_dec_ref(v_a_219_);
lean_dec_ref(v_e_218_);
v_a_285_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_255_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_255_);
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
v___jp_228_:
{
if (lean_obj_tag(v___y_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_246_; 
v_a_230_ = lean_ctor_get(v___y_229_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___y_229_);
if (v_isSharedCheck_246_ == 0)
{
v___x_232_ = v___y_229_;
v_isShared_233_ = v_isSharedCheck_246_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___y_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_246_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_unbox(v_a_230_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; uint8_t v___x_238_; lean_object* v___x_240_; 
v___x_235_ = lean_unsigned_to_nat(2u);
v___x_236_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_unbox(v_a_230_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_237_);
v___x_238_ = lean_unbox(v_a_230_);
lean_dec(v_a_230_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1 + 1, v___x_238_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_236_);
v___x_240_ = v___x_232_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_236_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_244_; 
lean_dec(v_a_230_);
v___x_242_ = lean_box(0);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_242_);
v___x_244_ = v___x_232_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___y_229_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___y_229_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___y_229_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___y_229_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object* v_e_293_, lean_object* v_a_294_, lean_object* v_b_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_293_, v_a_294_, v_b_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* v_e_304_, lean_object* v_a_305_, lean_object* v_b_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_304_, v_a_305_, v_b_306_, v_a_307_, v_a_311_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* v_e_319_, lean_object* v_a_320_, lean_object* v_b_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(v_e_319_, v_a_320_, v_b_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec(v_a_322_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_b_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___y_345_; lean_object* v___x_371_; 
lean_inc_ref(v_e_334_);
v___x_371_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_334_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_404_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_404_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_404_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_404_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint8_t v___x_376_; 
v___x_376_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_del_object(v___x_374_);
v___x_377_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_334_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_391_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_391_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_391_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_391_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_unbox(v_a_378_);
lean_dec(v_a_378_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec_ref(v_b_336_);
lean_dec_ref(v_a_335_);
v___x_383_ = lean_box(1);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
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
lean_object* v___x_387_; 
lean_del_object(v___x_380_);
v___x_387_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_335_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; uint8_t v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
v___x_389_ = lean_unbox(v_a_388_);
lean_dec(v_a_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_387_);
v___x_390_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
v___y_345_ = v___x_390_;
goto v___jp_344_;
}
else
{
lean_dec_ref(v_b_336_);
v___y_345_ = v___x_387_;
goto v___jp_344_;
}
}
else
{
lean_dec_ref(v_b_336_);
v___y_345_ = v___x_387_;
goto v___jp_344_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_b_336_);
lean_dec_ref(v_a_335_);
v_a_392_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_377_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_377_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_dec_ref(v_b_336_);
lean_dec_ref(v_a_335_);
lean_dec_ref(v_e_334_);
v___x_400_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_400_);
v___x_402_ = v___x_374_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_b_336_);
lean_dec_ref(v_a_335_);
lean_dec_ref(v_e_334_);
v_a_405_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_371_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_371_);
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
v___jp_344_:
{
if (lean_obj_tag(v___y_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_362_; 
v_a_346_ = lean_ctor_get(v___y_345_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___y_345_);
if (v_isSharedCheck_362_ == 0)
{
v___x_348_ = v___y_345_;
v_isShared_349_ = v_isSharedCheck_362_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___y_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_362_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint8_t v___x_350_; 
v___x_350_ = lean_unbox(v_a_346_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; uint8_t v___x_354_; lean_object* v___x_356_; 
v___x_351_ = lean_unsigned_to_nat(2u);
v___x_352_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_352_, 0, v___x_351_);
v___x_353_ = lean_unbox(v_a_346_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*1, v___x_353_);
v___x_354_ = lean_unbox(v_a_346_);
lean_dec(v_a_346_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*1 + 1, v___x_354_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_352_);
v___x_356_ = v___x_348_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_352_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec(v_a_346_);
v___x_358_ = lean_box(0);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_358_);
v___x_360_ = v___x_348_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___y_345_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___y_345_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___y_345_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___y_345_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_b_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_413_, v_a_414_, v_b_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_b_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_424_, v_a_425_, v_b_426_, v_a_427_, v_a_431_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* v_e_439_, lean_object* v_a_440_, lean_object* v_b_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(v_e_439_, v_a_440_, v_b_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec(v_a_442_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_b_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___y_468_; lean_object* v___y_491_; lean_object* v___y_510_; lean_object* v___y_533_; lean_object* v___x_548_; 
lean_inc_ref(v_e_454_);
v___x_548_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_454_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; uint8_t v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v___x_550_ = lean_unbox(v_a_549_);
lean_dec(v_a_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_454_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_565_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_565_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_565_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_565_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint8_t v___x_556_; 
v___x_556_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
v___x_557_ = lean_box(1);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; 
lean_del_object(v___x_554_);
lean_inc_ref(v_a_455_);
v___x_561_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_455_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; uint8_t v___x_563_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
v___x_563_ = lean_unbox(v_a_562_);
lean_dec(v_a_562_);
if (v___x_563_ == 0)
{
v___y_491_ = v___x_561_;
goto v___jp_490_;
}
else
{
lean_object* v___x_564_; 
lean_dec_ref(v___x_561_);
lean_inc_ref(v_b_456_);
v___x_564_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
v___y_491_ = v___x_564_;
goto v___jp_490_;
}
}
else
{
v___y_491_ = v___x_561_;
goto v___jp_490_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
v_a_566_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_551_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_551_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v___x_574_; 
lean_dec_ref(v_e_454_);
lean_inc_ref(v_a_455_);
v___x_574_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_455_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; uint8_t v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
v___x_576_ = lean_unbox(v_a_575_);
lean_dec(v_a_575_);
if (v___x_576_ == 0)
{
v___y_533_ = v___x_574_;
goto v___jp_532_;
}
else
{
lean_object* v___x_577_; 
lean_dec_ref(v___x_574_);
lean_inc_ref(v_b_456_);
v___x_577_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
v___y_533_ = v___x_577_;
goto v___jp_532_;
}
}
else
{
v___y_533_ = v___x_574_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
lean_dec_ref(v_e_454_);
v_a_578_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_548_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_548_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
v___jp_464_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_box(0);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
v___jp_467_:
{
if (lean_obj_tag(v___y_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_a_469_ = lean_ctor_get(v___y_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v___y_468_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___y_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = lean_unbox(v_a_469_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; uint8_t v___x_477_; lean_object* v___x_479_; 
v___x_474_ = lean_unsigned_to_nat(2u);
v___x_475_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___x_476_ = lean_unbox(v_a_469_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1, v___x_476_);
v___x_477_ = lean_unbox(v_a_469_);
lean_dec(v_a_469_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1 + 1, v___x_477_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_475_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_475_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
else
{
lean_del_object(v___x_471_);
lean_dec(v_a_469_);
goto v___jp_464_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___y_468_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___y_468_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___y_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
lean_object* v_a_492_; uint8_t v___x_493_; 
v_a_492_ = lean_ctor_get(v___y_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___y_491_);
v___x_493_ = lean_unbox(v_a_492_);
lean_dec(v_a_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_455_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; uint8_t v___x_496_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
v___x_496_ = lean_unbox(v_a_495_);
lean_dec(v_a_495_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_b_456_);
v___y_468_ = v___x_494_;
goto v___jp_467_;
}
else
{
lean_object* v___x_497_; 
lean_dec_ref(v___x_494_);
v___x_497_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
v___y_468_ = v___x_497_;
goto v___jp_467_;
}
}
else
{
lean_dec_ref(v_b_456_);
v___y_468_ = v___x_494_;
goto v___jp_467_;
}
}
else
{
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
goto v___jp_464_;
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
v_a_498_ = lean_ctor_get(v___y_491_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___y_491_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___y_491_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___y_491_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
v___jp_506_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
v___jp_509_:
{
if (lean_obj_tag(v___y_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_523_; 
v_a_511_ = lean_ctor_get(v___y_510_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___y_510_);
if (v_isSharedCheck_523_ == 0)
{
v___x_513_ = v___y_510_;
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___y_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___x_515_; 
v___x_515_ = lean_unbox(v_a_511_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; uint8_t v___x_519_; lean_object* v___x_521_; 
v___x_516_ = lean_unsigned_to_nat(2u);
v___x_517_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___x_518_ = lean_unbox(v_a_511_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1, v___x_518_);
v___x_519_ = lean_unbox(v_a_511_);
lean_dec(v_a_511_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1 + 1, v___x_519_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_517_);
v___x_521_ = v___x_513_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_517_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_del_object(v___x_513_);
lean_dec(v_a_511_);
goto v___jp_506_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___y_510_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___y_510_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___y_510_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___y_510_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
v___jp_532_:
{
if (lean_obj_tag(v___y_533_) == 0)
{
lean_object* v_a_534_; uint8_t v___x_535_; 
v_a_534_ = lean_ctor_get(v___y_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref(v___y_533_);
v___x_535_ = lean_unbox(v_a_534_);
lean_dec(v_a_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_455_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; uint8_t v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
v___x_538_ = lean_unbox(v_a_537_);
lean_dec(v_a_537_);
if (v___x_538_ == 0)
{
lean_dec_ref(v_b_456_);
v___y_510_ = v___x_536_;
goto v___jp_509_;
}
else
{
lean_object* v___x_539_; 
lean_dec_ref(v___x_536_);
v___x_539_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
v___y_510_ = v___x_539_;
goto v___jp_509_;
}
}
else
{
lean_dec_ref(v_b_456_);
v___y_510_ = v___x_536_;
goto v___jp_509_;
}
}
else
{
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
goto v___jp_506_;
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_b_456_);
lean_dec_ref(v_a_455_);
v_a_540_ = lean_ctor_get(v___y_533_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___y_533_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___y_533_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___y_533_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object* v_e_586_, lean_object* v_a_587_, lean_object* v_b_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_586_, v_a_587_, v_b_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_b_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_597_, v_a_598_, v_b_599_, v_a_600_, v_a_604_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* v_e_612_, lean_object* v_a_613_, lean_object* v_b_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(v_e_612_, v_a_613_, v_b_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec(v_a_615_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object* v_c_627_, uint8_t v___x_628_, uint8_t v_d_629_, lean_object* v_a_630_, lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
if (v_d_629_ == 0)
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_st_ref_get(v___y_632_);
v___x_644_ = l_Lean_Expr_isApp(v_a_630_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v___x_643_);
lean_dec_ref(v_a_630_);
lean_dec_ref(v_c_627_);
v___x_645_ = lean_box(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
else
{
uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_Meta_Grind_Goal_isCongruent(v___x_643_, v_c_627_, v_a_630_);
v___x_648_ = lean_box(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec_ref(v_a_630_);
lean_dec_ref(v_c_627_);
v___x_650_ = lean_box(v___x_628_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* v_c_652_, lean_object* v___x_653_, lean_object* v_d_654_, lean_object* v_a_655_, lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_10092__boxed_668_; uint8_t v_d_boxed_669_; lean_object* v_res_670_; 
v___x_10092__boxed_668_ = lean_unbox(v___x_653_);
v_d_boxed_669_ = lean_unbox(v_d_654_);
v_res_670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_652_, v___x_10092__boxed_668_, v_d_boxed_669_, v_a_655_, v_x_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(lean_object* v_f_671_, lean_object* v_keys_672_, lean_object* v_vals_673_, lean_object* v_i_674_, lean_object* v_acc_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_array_get_size(v_keys_672_);
v___x_688_ = lean_nat_dec_lt(v_i_674_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v_i_674_);
lean_dec_ref(v_f_671_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_acc_675_);
return v___x_689_;
}
else
{
lean_object* v_k_690_; lean_object* v_v_691_; lean_object* v___x_692_; 
v_k_690_ = lean_array_fget_borrowed(v_keys_672_, v_i_674_);
v_v_691_ = lean_array_fget_borrowed(v_vals_673_, v_i_674_);
lean_inc_ref(v_f_671_);
lean_inc(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc(v___y_676_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
v___x_692_ = lean_apply_14(v_f_671_, v_acc_675_, v_k_690_, v_v_691_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, lean_box(0));
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v___x_692_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_i_674_, v___x_694_);
lean_dec(v_i_674_);
v_i_674_ = v___x_695_;
v_acc_675_ = v_a_693_;
goto _start;
}
else
{
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v_i_674_);
lean_dec_ref(v_f_671_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_697_, lean_object* v_keys_698_, lean_object* v_vals_699_, lean_object* v_i_700_, lean_object* v_acc_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_697_, v_keys_698_, v_vals_699_, v_i_700_, v_acc_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec_ref(v_vals_699_);
lean_dec_ref(v_keys_698_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* v_f_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v_es_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_748_; 
v_es_728_ = lean_ctor_get(v_x_715_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_748_ == 0)
{
v___x_730_ = v_x_715_;
v_isShared_731_ = v_isSharedCheck_748_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_es_728_);
lean_dec(v_x_715_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_748_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_es_728_);
v___x_734_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; 
lean_dec_ref(v_es_728_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v_f_714_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_x_716_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_x_716_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
uint8_t v___x_738_; 
v___x_738_ = lean_nat_dec_le(v___x_733_, v___x_733_);
if (v___x_738_ == 0)
{
if (v___x_734_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v_es_728_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v_f_714_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_x_716_);
v___x_740_ = v___x_730_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_x_716_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
lean_del_object(v___x_730_);
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_733_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_714_, v_es_728_, v___x_742_, v___x_743_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec_ref(v_es_728_);
return v___x_744_;
}
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_730_);
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_733_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_714_, v_es_728_, v___x_745_, v___x_746_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec_ref(v_es_728_);
return v___x_747_;
}
}
}
}
else
{
lean_object* v_ks_749_; lean_object* v_vs_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_ks_749_ = lean_ctor_get(v_x_715_, 0);
lean_inc_ref(v_ks_749_);
v_vs_750_ = lean_ctor_get(v_x_715_, 1);
lean_inc_ref(v_vs_750_);
lean_dec_ref(v_x_715_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_714_, v_ks_749_, v_vs_750_, v___x_751_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec_ref(v_vs_750_);
lean_dec_ref(v_ks_749_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* v_f_753_, lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_a_770_; lean_object* v___y_775_; uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
switch(lean_obj_tag(v___x_778_))
{
case 0:
{
lean_object* v_key_779_; lean_object* v_val_780_; lean_object* v___x_781_; 
v_key_779_ = lean_ctor_get(v___x_778_, 0);
v_val_780_ = lean_ctor_get(v___x_778_, 1);
lean_inc_ref(v_f_753_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc(v___y_758_);
lean_inc(v_val_780_);
lean_inc(v_key_779_);
v___x_781_ = lean_apply_14(v_f_753_, v_b_757_, v_key_779_, v_val_780_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, lean_box(0));
v___y_775_ = v___x_781_;
goto v___jp_774_;
}
case 1:
{
lean_object* v_node_782_; lean_object* v___x_783_; 
v_node_782_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc(v___y_758_);
lean_inc(v_node_782_);
lean_inc_ref(v_f_753_);
v___x_783_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_753_, v_node_782_, v_b_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
v___y_775_ = v___x_783_;
goto v___jp_774_;
}
default: 
{
v_a_770_ = v_b_757_;
goto v___jp_769_;
}
}
}
else
{
lean_object* v___x_784_; 
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v_f_753_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_b_757_);
return v___x_784_;
}
v___jp_769_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_755_, v___x_771_);
v_i_755_ = v___x_772_;
v_b_757_ = v_a_770_;
goto _start;
}
v___jp_774_:
{
if (lean_obj_tag(v___y_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___y_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___y_775_);
v_a_770_ = v_a_776_;
goto v___jp_769_;
}
else
{
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v_f_753_);
return v___y_775_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_785_, lean_object* v_as_786_, lean_object* v_i_787_, lean_object* v_stop_788_, lean_object* v_b_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
size_t v_i_boxed_801_; size_t v_stop_boxed_802_; lean_object* v_res_803_; 
v_i_boxed_801_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_stop_boxed_802_ = lean_unbox_usize(v_stop_788_);
lean_dec(v_stop_788_);
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_785_, v_as_786_, v_i_boxed_801_, v_stop_boxed_802_, v_b_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_as_786_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_804_, v_x_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* v_c_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_Expr_isApp(v_c_819_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_c_819_);
v___x_832_ = lean_box(v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v_toGoalState_835_; lean_object* v_split_836_; lean_object* v_resolved_837_; lean_object* v___x_838_; lean_object* v___f_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_834_ = lean_st_ref_get(v_a_820_);
v_toGoalState_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc_ref(v_toGoalState_835_);
lean_dec(v___x_834_);
v_split_836_ = lean_ctor_get(v_toGoalState_835_, 15);
lean_inc_ref(v_split_836_);
lean_dec_ref(v_toGoalState_835_);
v_resolved_837_ = lean_ctor_get(v_split_836_, 3);
lean_inc_ref(v_resolved_837_);
lean_dec_ref(v_split_836_);
v___x_838_ = lean_box(v___x_831_);
v___f_839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 16, 2);
lean_closure_set(v___f_839_, 0, v_c_819_);
lean_closure_set(v___f_839_, 1, v___x_838_);
v___x_840_ = 0;
v___x_841_ = lean_box(v___x_840_);
v___x_842_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v___f_839_, v_resolved_837_, v___x_841_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object* v_c_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* v_map_856_, lean_object* v_f_857_, lean_object* v_init_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_857_, v_map_856_, v_init_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* v_map_871_, lean_object* v_f_872_, lean_object* v_init_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_871_, v_f_872_, v_init_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* v_00_u03c3_886_, lean_object* v_00_u03b2_887_, lean_object* v_map_888_, lean_object* v_f_889_, lean_object* v_init_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_889_, v_map_888_, v_init_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* v_00_u03c3_903_, lean_object* v_00_u03b2_904_, lean_object* v_map_905_, lean_object* v_f_906_, lean_object* v_init_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(v_00_u03c3_903_, v_00_u03b2_904_, v_map_905_, v_f_906_, v_init_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* v_00_u03c3_920_, lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_f_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_923_, v_x_924_, v_x_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_938_ = _args[0];
lean_object* v_00_u03b1_939_ = _args[1];
lean_object* v_00_u03b2_940_ = _args[2];
lean_object* v_f_941_ = _args[3];
lean_object* v_x_942_ = _args[4];
lean_object* v_x_943_ = _args[5];
lean_object* v___y_944_ = _args[6];
lean_object* v___y_945_ = _args[7];
lean_object* v___y_946_ = _args[8];
lean_object* v___y_947_ = _args[9];
lean_object* v___y_948_ = _args[10];
lean_object* v___y_949_ = _args[11];
lean_object* v___y_950_ = _args[12];
lean_object* v___y_951_ = _args[13];
lean_object* v___y_952_ = _args[14];
lean_object* v___y_953_ = _args[15];
lean_object* v___y_954_ = _args[16];
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(v_00_u03c3_938_, v_00_u03b1_939_, v_00_u03b2_940_, v_f_941_, v_x_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_00_u03c3_958_, lean_object* v_f_959_, lean_object* v_as_960_, size_t v_i_961_, size_t v_stop_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_959_, v_as_960_, v_i_961_, v_stop_962_, v_b_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_976_ = _args[0];
lean_object* v_00_u03b2_977_ = _args[1];
lean_object* v_00_u03c3_978_ = _args[2];
lean_object* v_f_979_ = _args[3];
lean_object* v_as_980_ = _args[4];
lean_object* v_i_981_ = _args[5];
lean_object* v_stop_982_ = _args[6];
lean_object* v_b_983_ = _args[7];
lean_object* v___y_984_ = _args[8];
lean_object* v___y_985_ = _args[9];
lean_object* v___y_986_ = _args[10];
lean_object* v___y_987_ = _args[11];
lean_object* v___y_988_ = _args[12];
lean_object* v___y_989_ = _args[13];
lean_object* v___y_990_ = _args[14];
lean_object* v___y_991_ = _args[15];
lean_object* v___y_992_ = _args[16];
lean_object* v___y_993_ = _args[17];
lean_object* v___y_994_ = _args[18];
_start:
{
size_t v_i_boxed_995_; size_t v_stop_boxed_996_; lean_object* v_res_997_; 
v_i_boxed_995_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_stop_boxed_996_ = lean_unbox_usize(v_stop_982_);
lean_dec(v_stop_982_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(v_00_u03b1_976_, v_00_u03b2_977_, v_00_u03c3_978_, v_f_979_, v_as_980_, v_i_boxed_995_, v_stop_boxed_996_, v_b_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec_ref(v_as_980_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_998_, lean_object* v_00_u03b1_999_, lean_object* v_00_u03b2_1000_, lean_object* v_f_1001_, lean_object* v_keys_1002_, lean_object* v_vals_1003_, lean_object* v_heq_1004_, lean_object* v_i_1005_, lean_object* v_acc_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_1001_, v_keys_1002_, v_vals_1003_, v_i_1005_, v_acc_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_1019_ = _args[0];
lean_object* v_00_u03b1_1020_ = _args[1];
lean_object* v_00_u03b2_1021_ = _args[2];
lean_object* v_f_1022_ = _args[3];
lean_object* v_keys_1023_ = _args[4];
lean_object* v_vals_1024_ = _args[5];
lean_object* v_heq_1025_ = _args[6];
lean_object* v_i_1026_ = _args[7];
lean_object* v_acc_1027_ = _args[8];
lean_object* v___y_1028_ = _args[9];
lean_object* v___y_1029_ = _args[10];
lean_object* v___y_1030_ = _args[11];
lean_object* v___y_1031_ = _args[12];
lean_object* v___y_1032_ = _args[13];
lean_object* v___y_1033_ = _args[14];
lean_object* v___y_1034_ = _args[15];
lean_object* v___y_1035_ = _args[16];
lean_object* v___y_1036_ = _args[17];
lean_object* v___y_1037_ = _args[18];
lean_object* v___y_1038_ = _args[19];
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(v_00_u03c3_1019_, v_00_u03b1_1020_, v_00_u03b2_1021_, v_f_1022_, v_keys_1023_, v_vals_1024_, v_heq_1025_, v_i_1026_, v_acc_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec_ref(v_vals_1024_);
lean_dec_ref(v_keys_1023_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_options_1046_; uint8_t v_hasTrace_1047_; 
v_options_1046_ = lean_ctor_get(v___y_1044_, 2);
v_hasTrace_1047_ = lean_ctor_get_uint8(v_options_1046_, sizeof(void*)*1);
if (v_hasTrace_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v_cls_1043_);
v___x_1048_ = lean_box(v_hasTrace_1047_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v_inheritedTraceOptions_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_inheritedTraceOptions_1050_ = lean_ctor_get(v___y_1044_, 13);
v___x_1051_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1052_ = l_Lean_Name_append(v___x_1051_, v_cls_1043_);
v___x_1053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1050_, v_options_1046_, v___x_1052_);
lean_dec(v___x_1052_);
v___x_1054_ = lean_box(v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1056_, v___y_1057_);
lean_dec_ref(v___y_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1060_, v___y_1069_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3(lean_object* v_msgData_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v_env_1093_; lean_object* v___x_1094_; lean_object* v_mctx_1095_; lean_object* v_lctx_1096_; lean_object* v_options_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1092_ = lean_st_ref_get(v___y_1090_);
v_env_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc_ref(v_env_1093_);
lean_dec(v___x_1092_);
v___x_1094_ = lean_st_ref_get(v___y_1088_);
v_mctx_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_mctx_1095_);
lean_dec(v___x_1094_);
v_lctx_1096_ = lean_ctor_get(v___y_1087_, 2);
v_options_1097_ = lean_ctor_get(v___y_1089_, 2);
lean_inc_ref(v_options_1097_);
lean_inc_ref(v_lctx_1096_);
v___x_1098_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1098_, 0, v_env_1093_);
lean_ctor_set(v___x_1098_, 1, v_mctx_1095_);
lean_ctor_set(v___x_1098_, 2, v_lctx_1096_);
lean_ctor_set(v___x_1098_, 3, v_options_1097_);
v___x_1099_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_msgData_1086_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3___boxed(lean_object* v_msgData_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3(v_msgData_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1108_; double v___x_1109_; 
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_float_of_nat(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(lean_object* v_cls_1113_, lean_object* v_msg_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_ref_1120_; lean_object* v___x_1121_; lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1166_; 
v_ref_1120_ = lean_ctor_get(v___y_1117_, 5);
v___x_1121_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3(v_msg_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1166_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1166_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v_traceState_1127_; lean_object* v_env_1128_; lean_object* v_nextMacroScope_1129_; lean_object* v_ngen_1130_; lean_object* v_auxDeclNGen_1131_; lean_object* v_cache_1132_; lean_object* v_messages_1133_; lean_object* v_infoState_1134_; lean_object* v_snapshotTasks_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1165_; 
v___x_1126_ = lean_st_ref_take(v___y_1118_);
v_traceState_1127_ = lean_ctor_get(v___x_1126_, 4);
v_env_1128_ = lean_ctor_get(v___x_1126_, 0);
v_nextMacroScope_1129_ = lean_ctor_get(v___x_1126_, 1);
v_ngen_1130_ = lean_ctor_get(v___x_1126_, 2);
v_auxDeclNGen_1131_ = lean_ctor_get(v___x_1126_, 3);
v_cache_1132_ = lean_ctor_get(v___x_1126_, 5);
v_messages_1133_ = lean_ctor_get(v___x_1126_, 6);
v_infoState_1134_ = lean_ctor_get(v___x_1126_, 7);
v_snapshotTasks_1135_ = lean_ctor_get(v___x_1126_, 8);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1137_ = v___x_1126_;
v_isShared_1138_ = v_isSharedCheck_1165_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snapshotTasks_1135_);
lean_inc(v_infoState_1134_);
lean_inc(v_messages_1133_);
lean_inc(v_cache_1132_);
lean_inc(v_traceState_1127_);
lean_inc(v_auxDeclNGen_1131_);
lean_inc(v_ngen_1130_);
lean_inc(v_nextMacroScope_1129_);
lean_inc(v_env_1128_);
lean_dec(v___x_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1165_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint64_t v_tid_1139_; lean_object* v_traces_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1164_; 
v_tid_1139_ = lean_ctor_get_uint64(v_traceState_1127_, sizeof(void*)*1);
v_traces_1140_ = lean_ctor_get(v_traceState_1127_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_traceState_1127_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1142_ = v_traceState_1127_;
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_traces_1140_);
lean_dec(v_traceState_1127_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; double v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__0);
v___x_1146_ = 0;
v___x_1147_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__1));
v___x_1148_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1148_, 0, v_cls_1113_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
lean_ctor_set(v___x_1148_, 2, v___x_1147_);
lean_ctor_set_float(v___x_1148_, sizeof(void*)*3, v___x_1145_);
lean_ctor_set_float(v___x_1148_, sizeof(void*)*3 + 8, v___x_1145_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*3 + 16, v___x_1146_);
v___x_1149_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___closed__2));
v___x_1150_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v_a_1122_);
lean_ctor_set(v___x_1150_, 2, v___x_1149_);
lean_inc(v_ref_1120_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_ref_1120_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_PersistentArray_push___redArg(v_traces_1140_, v___x_1151_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1152_);
v___x_1154_ = v___x_1142_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1152_);
lean_ctor_set_uint64(v_reuseFailAlloc_1163_, sizeof(void*)*1, v_tid_1139_);
v___x_1154_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 4, v___x_1154_);
v___x_1156_ = v___x_1137_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_env_1128_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_nextMacroScope_1129_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_ngen_1130_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_auxDeclNGen_1131_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_cache_1132_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_messages_1133_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_infoState_1134_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_snapshotTasks_1135_);
v___x_1156_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1157_ = lean_st_ref_set(v___y_1118_, v___x_1156_);
v___x_1158_ = lean_box(0);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1158_);
v___x_1160_ = v___x_1124_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg___boxed(lean_object* v_cls_1167_, lean_object* v_msg_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(v_cls_1167_, v_msg_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_ref_1181_; lean_object* v___x_1182_; lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_ref_1181_ = lean_ctor_get(v___y_1178_, 5);
v___x_1182_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2_spec__3(v_msg_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_inc(v_ref_1181_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_ref_1181_);
lean_ctor_set(v___x_1187_, 1, v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 1);
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg(v_msg_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1199_, lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_fileName_1212_; lean_object* v_fileMap_1213_; lean_object* v_options_1214_; lean_object* v_currRecDepth_1215_; lean_object* v_maxRecDepth_1216_; lean_object* v_ref_1217_; lean_object* v_currNamespace_1218_; lean_object* v_openDecls_1219_; lean_object* v_initHeartbeats_1220_; lean_object* v_maxHeartbeats_1221_; lean_object* v_quotContext_1222_; lean_object* v_currMacroScope_1223_; uint8_t v_diag_1224_; lean_object* v_cancelTk_x3f_1225_; uint8_t v_suppressElabErrors_1226_; lean_object* v_inheritedTraceOptions_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1236_; 
v_fileName_1212_ = lean_ctor_get(v___y_1209_, 0);
v_fileMap_1213_ = lean_ctor_get(v___y_1209_, 1);
v_options_1214_ = lean_ctor_get(v___y_1209_, 2);
v_currRecDepth_1215_ = lean_ctor_get(v___y_1209_, 3);
v_maxRecDepth_1216_ = lean_ctor_get(v___y_1209_, 4);
v_ref_1217_ = lean_ctor_get(v___y_1209_, 5);
v_currNamespace_1218_ = lean_ctor_get(v___y_1209_, 6);
v_openDecls_1219_ = lean_ctor_get(v___y_1209_, 7);
v_initHeartbeats_1220_ = lean_ctor_get(v___y_1209_, 8);
v_maxHeartbeats_1221_ = lean_ctor_get(v___y_1209_, 9);
v_quotContext_1222_ = lean_ctor_get(v___y_1209_, 10);
v_currMacroScope_1223_ = lean_ctor_get(v___y_1209_, 11);
v_diag_1224_ = lean_ctor_get_uint8(v___y_1209_, sizeof(void*)*14);
v_cancelTk_x3f_1225_ = lean_ctor_get(v___y_1209_, 12);
v_suppressElabErrors_1226_ = lean_ctor_get_uint8(v___y_1209_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1227_ = lean_ctor_get(v___y_1209_, 13);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___y_1209_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1229_ = v___y_1209_;
v_isShared_1230_ = v_isSharedCheck_1236_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_inheritedTraceOptions_1227_);
lean_inc(v_cancelTk_x3f_1225_);
lean_inc(v_currMacroScope_1223_);
lean_inc(v_quotContext_1222_);
lean_inc(v_maxHeartbeats_1221_);
lean_inc(v_initHeartbeats_1220_);
lean_inc(v_openDecls_1219_);
lean_inc(v_currNamespace_1218_);
lean_inc(v_ref_1217_);
lean_inc(v_maxRecDepth_1216_);
lean_inc(v_currRecDepth_1215_);
lean_inc(v_options_1214_);
lean_inc(v_fileMap_1213_);
lean_inc(v_fileName_1212_);
lean_dec(v___y_1209_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1236_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_ref_1231_; lean_object* v___x_1233_; 
v_ref_1231_ = l_Lean_replaceRef(v_ref_1199_, v_ref_1217_);
lean_dec(v_ref_1217_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 5, v_ref_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fileName_1212_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_fileMap_1213_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_options_1214_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_currRecDepth_1215_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_maxRecDepth_1216_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v_ref_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_currNamespace_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 7, v_openDecls_1219_);
lean_ctor_set(v_reuseFailAlloc_1235_, 8, v_initHeartbeats_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 9, v_maxHeartbeats_1221_);
lean_ctor_set(v_reuseFailAlloc_1235_, 10, v_quotContext_1222_);
lean_ctor_set(v_reuseFailAlloc_1235_, 11, v_currMacroScope_1223_);
lean_ctor_set(v_reuseFailAlloc_1235_, 12, v_cancelTk_x3f_1225_);
lean_ctor_set(v_reuseFailAlloc_1235_, 13, v_inheritedTraceOptions_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*14, v_diag_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*14 + 1, v_suppressElabErrors_1226_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg(v_msg_1200_, v___y_1207_, v___y_1208_, v___x_1233_, v___y_1210_);
lean_dec_ref(v___x_1233_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1237_, v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v_ref_1237_);
return v_res_1250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1251_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
lean_ctor_set(v___x_1256_, 3, v___x_1254_);
lean_ctor_set(v___x_1256_, 4, v___x_1254_);
lean_ctor_set(v___x_1256_, 5, v___x_1254_);
lean_ctor_set(v___x_1256_, 6, v___x_1254_);
lean_ctor_set(v___x_1256_, 7, v___x_1254_);
lean_ctor_set(v___x_1256_, 8, v___x_1254_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_unsigned_to_nat(32u);
v___x_1258_ = lean_mk_empty_array_with_capacity(v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1260_ = ((size_t)5ULL);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_unsigned_to_nat(32u);
v___x_1263_ = lean_mk_empty_array_with_capacity(v___x_1262_);
v___x_1264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1265_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___x_1263_);
lean_ctor_set(v___x_1265_, 2, v___x_1261_);
lean_ctor_set(v___x_1265_, 3, v___x_1261_);
lean_ctor_set_usize(v___x_1265_, 4, v___x_1260_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = lean_box(1);
v___x_1267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_1268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1267_);
lean_ctor_set(v___x_1269_, 2, v___x_1266_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1291_, lean_object* v_declHint_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_env_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_st_ref_get(v___y_1293_);
v_env_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_ref(v_env_1296_);
lean_dec(v___x_1295_);
v___x_1297_ = l_Lean_Name_isAnonymous(v_declHint_1292_);
if (v___x_1297_ == 0)
{
uint8_t v_isExporting_1298_; 
v_isExporting_1298_ = lean_ctor_get_uint8(v_env_1296_, sizeof(void*)*8);
if (v_isExporting_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref(v_env_1296_);
lean_dec(v_declHint_1292_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_msg_1291_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
lean_inc_ref(v_env_1296_);
v___x_1300_ = l_Lean_Environment_setExporting(v_env_1296_, v___x_1297_);
lean_inc(v_declHint_1292_);
lean_inc_ref(v___x_1300_);
v___x_1301_ = l_Lean_Environment_contains(v___x_1300_, v_declHint_1292_, v_isExporting_1298_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_env_1296_);
lean_dec(v_declHint_1292_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_msg_1291_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_c_1308_; lean_object* v___x_1309_; 
v___x_1303_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_1304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1305_ = l_Lean_Options_empty;
v___x_1306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1300_);
lean_ctor_set(v___x_1306_, 1, v___x_1303_);
lean_ctor_set(v___x_1306_, 2, v___x_1304_);
lean_ctor_set(v___x_1306_, 3, v___x_1305_);
lean_inc(v_declHint_1292_);
v___x_1307_ = l_Lean_MessageData_ofConstName(v_declHint_1292_, v___x_1297_);
v_c_1308_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1308_, 0, v___x_1306_);
lean_ctor_set(v_c_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1296_, v_declHint_1292_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref(v_env_1296_);
lean_dec(v_declHint_1292_);
v___x_1310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_c_1308_);
v___x_1312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_MessageData_note(v___x_1313_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_msg_1291_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
else
{
lean_object* v_val_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1352_; 
v_val_1317_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1319_ = v___x_1309_;
v_isShared_1320_ = v_isSharedCheck_1352_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_val_1317_);
lean_dec(v___x_1309_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1352_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_mod_1324_; uint8_t v___x_1325_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = l_Lean_Environment_header(v_env_1296_);
lean_dec_ref(v_env_1296_);
v___x_1323_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1322_);
v_mod_1324_ = lean_array_get(v___x_1321_, v___x_1323_, v_val_1317_);
lean_dec(v_val_1317_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = l_Lean_isPrivateName(v_declHint_1292_);
lean_dec(v_declHint_1292_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v_c_1308_);
v___x_1328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_ofName(v_mod_1324_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_MessageData_note(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_msg_1291_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1335_);
v___x_1337_ = v___x_1319_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1339_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v_c_1308_);
v___x_1341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_MessageData_ofName(v_mod_1324_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = l_Lean_MessageData_note(v___x_1346_);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_msg_1291_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1348_);
v___x_1350_ = v___x_1319_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1353_; 
lean_dec_ref(v_env_1296_);
lean_dec(v_declHint_1292_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_msg_1291_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1354_, lean_object* v_declHint_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1354_, v_declHint_1355_, v___y_1356_);
lean_dec(v___y_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_1359_, lean_object* v_declHint_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1382_; 
v___x_1372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1359_, v_declHint_1360_, v___y_1370_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = l_Lean_unknownIdentifierMessageTag;
v___x_1378_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_a_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_1383_, lean_object* v_declHint_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1383_, v_declHint_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_1397_, lean_object* v_msg_1398_, lean_object* v_declHint_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1398_, v_declHint_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1397_, v_a_1412_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1414_, lean_object* v_msg_1415_, lean_object* v_declHint_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1414_, v_msg_1415_, v_declHint_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v_ref_1414_);
return v_res_1428_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1435_, lean_object* v_constName_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1448_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1449_ = 0;
lean_inc(v_constName_1436_);
v___x_1450_ = l_Lean_MessageData_ofConstName(v_constName_1436_, v___x_1449_);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1448_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1435_, v___x_1453_, v_constName_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1455_, lean_object* v_constName_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg(v_ref_1455_, v_constName_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v_ref_1455_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_ref_1481_; lean_object* v___x_1482_; 
v_ref_1481_ = lean_ctor_get(v___y_1478_, 5);
lean_inc(v_ref_1481_);
v___x_1482_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg(v_ref_1481_, v_constName_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v_ref_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v_env_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = lean_st_ref_get(v___y_1506_);
v_env_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc_ref(v_env_1509_);
lean_dec(v___x_1508_);
v___x_1510_ = 0;
lean_inc(v_constName_1496_);
v___x_1511_ = l_Lean_Environment_find_x3f(v_env_1509_, v_constName_1496_, v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1512_;
}
else
{
lean_object* v_val_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___y_1505_);
lean_dec(v_constName_1496_);
v_val_1513_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1511_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_val_1513_);
lean_dec(v___x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 0);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_val_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec(v___y_1522_);
return v_res_1533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
uint8_t v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; uint8_t v___y_1704_; lean_object* v___x_1816_; 
lean_inc_ref(v_e_1559_);
v___x_1816_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1559_, v_a_1567_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1858_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1858_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1858_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = l_Lean_Expr_cleanupAnnotations(v_a_1817_);
v___x_1835_ = l_Lean_Expr_isApp(v___x_1834_);
if (v___x_1835_ == 0)
{
lean_dec_ref(v___x_1834_);
lean_del_object(v___x_1819_);
v___y_1822_ = v_a_1560_;
v___y_1823_ = v_a_1561_;
v___y_1824_ = v_a_1562_;
v___y_1825_ = v_a_1563_;
v___y_1826_ = v_a_1564_;
v___y_1827_ = v_a_1565_;
v___y_1828_ = v_a_1566_;
v___y_1829_ = v_a_1567_;
v___y_1830_ = v_a_1568_;
v___y_1831_ = v_a_1569_;
goto v___jp_1821_;
}
else
{
lean_object* v_arg_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_arg_1836_ = lean_ctor_get(v___x_1834_, 1);
lean_inc_ref(v_arg_1836_);
v___x_1837_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1834_);
v___x_1838_ = l_Lean_Expr_isApp(v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_arg_1836_);
lean_del_object(v___x_1819_);
v___y_1822_ = v_a_1560_;
v___y_1823_ = v_a_1561_;
v___y_1824_ = v_a_1562_;
v___y_1825_ = v_a_1563_;
v___y_1826_ = v_a_1564_;
v___y_1827_ = v_a_1565_;
v___y_1828_ = v_a_1566_;
v___y_1829_ = v_a_1567_;
v___y_1830_ = v_a_1568_;
v___y_1831_ = v_a_1569_;
goto v___jp_1821_;
}
else
{
lean_object* v_arg_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_arg_1839_ = lean_ctor_get(v___x_1837_, 1);
lean_inc_ref(v_arg_1839_);
v___x_1840_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1837_);
v___x_1841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1842_ = l_Lean_Expr_isConstOf(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13));
v___x_1844_ = l_Lean_Expr_isConstOf(v___x_1840_, v___x_1843_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_isApp(v___x_1840_);
if (v___x_1845_ == 0)
{
lean_dec_ref(v___x_1840_);
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
lean_del_object(v___x_1819_);
v___y_1822_ = v_a_1560_;
v___y_1823_ = v_a_1561_;
v___y_1824_ = v_a_1562_;
v___y_1825_ = v_a_1563_;
v___y_1826_ = v_a_1564_;
v___y_1827_ = v_a_1565_;
v___y_1828_ = v_a_1566_;
v___y_1829_ = v_a_1567_;
v___y_1830_ = v_a_1568_;
v___y_1831_ = v_a_1569_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1840_);
v___x_1847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15));
v___x_1848_ = l_Lean_Expr_isConstOf(v___x_1846_, v___x_1847_);
lean_dec_ref(v___x_1846_);
if (v___x_1848_ == 0)
{
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
lean_del_object(v___x_1819_);
v___y_1822_ = v_a_1560_;
v___y_1823_ = v_a_1561_;
v___y_1824_ = v_a_1562_;
v___y_1825_ = v_a_1563_;
v___y_1826_ = v_a_1564_;
v___y_1827_ = v_a_1565_;
v___y_1828_ = v_a_1566_;
v___y_1829_ = v_a_1567_;
v___y_1830_ = v_a_1568_;
v___y_1831_ = v_a_1569_;
goto v___jp_1821_;
}
else
{
uint8_t v___x_1849_; 
lean_dec(v_a_1565_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_inc_ref(v_e_1559_);
v___x_1849_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1559_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec_ref(v_arg_1839_);
lean_dec_ref(v_arg_1836_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1559_);
v___x_1850_ = lean_unsigned_to_nat(2u);
v___x_1851_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*1, v___x_1849_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*1 + 1, v___x_1849_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1851_);
v___x_1853_ = v___x_1819_;
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
lean_del_object(v___x_1819_);
v___x_1855_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1559_, v_arg_1839_, v_arg_1836_, v_a_1560_, v_a_1564_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1560_);
return v___x_1855_;
}
}
}
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1840_);
lean_del_object(v___x_1819_);
lean_dec(v_a_1565_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
v___x_1856_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1559_, v_arg_1839_, v_arg_1836_, v_a_1560_, v_a_1564_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1560_);
return v___x_1856_;
}
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v___x_1840_);
lean_del_object(v___x_1819_);
lean_dec(v_a_1565_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
v___x_1857_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1559_, v_arg_1839_, v_arg_1836_, v_a_1560_, v_a_1564_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1560_);
return v___x_1857_;
}
}
}
v___jp_1821_:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_Meta_Grind_isIte(v_e_1559_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Lean_Meta_Grind_isDIte(v_e_1559_);
v___y_1694_ = v___y_1822_;
v___y_1695_ = v___y_1829_;
v___y_1696_ = v___y_1824_;
v___y_1697_ = v___y_1825_;
v___y_1698_ = v___y_1831_;
v___y_1699_ = v___y_1830_;
v___y_1700_ = v___y_1826_;
v___y_1701_ = v___y_1828_;
v___y_1702_ = v___y_1827_;
v___y_1703_ = v___y_1823_;
v___y_1704_ = v___x_1833_;
goto v___jp_1693_;
}
else
{
v___y_1694_ = v___y_1822_;
v___y_1695_ = v___y_1829_;
v___y_1696_ = v___y_1824_;
v___y_1697_ = v___y_1825_;
v___y_1698_ = v___y_1831_;
v___y_1699_ = v___y_1830_;
v___y_1700_ = v___y_1826_;
v___y_1701_ = v___y_1828_;
v___y_1702_ = v___y_1827_;
v___y_1703_ = v___y_1823_;
v___y_1704_ = v___x_1832_;
goto v___jp_1693_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1559_);
v_a_1859_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1816_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1816_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
v___jp_1571_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
v___jp_1577_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
v___jp_1580_:
{
uint8_t v___x_1592_; 
v___x_1592_ = l_Lean_Expr_isFVar(v_e_1559_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v_e_1559_);
v___x_1593_ = lean_box(1);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; 
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc_ref(v_e_1559_);
v___x_1595_ = lean_infer_type(v_e_1559_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
v___x_1597_ = l_Lean_Meta_whnfD(v_a_1596_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1599_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = l_Lean_Expr_getAppFn(v_a_1598_);
if (lean_obj_tag(v___x_1599_) == 4)
{
lean_object* v_declName_1600_; lean_object* v___x_1601_; 
v_declName_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_declName_1600_);
lean_dec_ref(v___x_1599_);
lean_inc_ref(v___y_1590_);
v___x_1601_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1600_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1582_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1641_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1641_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1641_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
if (lean_obj_tag(v_a_1602_) == 5)
{
lean_object* v_val_1606_; lean_object* v_ctors_1607_; uint8_t v_isRec_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
lean_dec(v_a_1598_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v_e_1559_);
v_val_1606_ = lean_ctor_get(v_a_1602_, 0);
lean_inc_ref(v_val_1606_);
lean_dec_ref(v_a_1602_);
v_ctors_1607_ = lean_ctor_get(v_val_1606_, 4);
lean_inc(v_ctors_1607_);
v_isRec_1608_ = lean_ctor_get_uint8(v_val_1606_, sizeof(void*)*6);
lean_dec_ref(v_val_1606_);
v___x_1609_ = l_List_lengthTR___redArg(v_ctors_1607_);
lean_dec(v_ctors_1607_);
v___x_1610_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*1, v_isRec_1608_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*1 + 1, v___y_1581_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1610_);
v___x_1612_ = v___x_1604_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
else
{
lean_object* v___x_1614_; 
lean_del_object(v___x_1604_);
lean_dec(v_a_1602_);
v___x_1614_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_1584_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; uint8_t v_verbose_1616_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
v_verbose_1616_ = lean_ctor_get_uint8(v_a_1615_, sizeof(void*)*11 + 15);
lean_dec(v_a_1615_);
if (v_verbose_1616_ == 0)
{
lean_dec(v_a_1598_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1617_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1618_ = l_Lean_MessageData_ofExpr(v_e_1559_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_indentExpr(v_a_1598_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_Meta_Grind_reportIssue(v___x_1623_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref(v___x_1624_);
goto v___jp_1574_;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1598_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v_e_1559_);
v_a_1633_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1614_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1614_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_a_1598_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v_e_1559_);
v_a_1642_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1601_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1601_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v___x_1650_; 
lean_dec_ref(v___x_1599_);
lean_dec(v___y_1582_);
v___x_1650_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_1584_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; uint8_t v_verbose_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v_verbose_1652_ = lean_ctor_get_uint8(v_a_1651_, sizeof(void*)*11 + 15);
lean_dec(v_a_1651_);
if (v_verbose_1652_ == 0)
{
lean_dec(v_a_1598_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1577_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1654_ = l_Lean_MessageData_ofExpr(v_e_1559_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_indentExpr(v_a_1598_);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_Meta_Grind_reportIssue(v___x_1659_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_dec_ref(v___x_1660_);
goto v___jp_1577_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_a_1598_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v_e_1559_);
v_a_1669_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1650_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1650_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v_e_1559_);
v_a_1677_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1597_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1597_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v_e_1559_);
v_a_1685_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1595_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1595_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
v___jp_1693_:
{
if (v___y_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1559_, v___y_1694_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1703_);
lean_inc(v___y_1694_);
lean_inc_ref(v_e_1559_);
v___x_1708_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1559_, v___y_1694_, v___y_1703_, v___y_1696_, v___y_1697_, v___y_1700_, v___y_1702_, v___y_1701_, v___y_1695_, v___y_1699_, v___y_1698_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1768_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1768_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1768_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_unbox(v_a_1709_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v_env_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_st_ref_get(v___y_1698_);
v_env_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc_ref(v_env_1715_);
lean_dec(v___x_1714_);
v___x_1716_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1715_, v_e_1559_);
if (lean_obj_tag(v___x_1716_) == 1)
{
lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1723_; 
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v_val_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1717_);
lean_dec(v_val_1717_);
v___x_1719_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
v___x_1720_ = lean_unbox(v_a_1709_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1, v___x_1720_);
v___x_1721_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1 + 1, v___x_1721_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1719_);
v___x_1723_ = v___x_1711_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1719_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
else
{
lean_object* v___x_1725_; 
lean_dec(v___x_1716_);
lean_del_object(v___x_1711_);
v___x_1725_ = l_Lean_Expr_getAppFn(v_e_1559_);
if (lean_obj_tag(v___x_1725_) == 4)
{
lean_object* v_declName_1726_; lean_object* v___x_1727_; 
v_declName_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_declName_1726_);
lean_dec_ref(v___x_1725_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1701_);
v___x_1727_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1726_, v___y_1701_, v___y_1695_, v___y_1699_, v___y_1698_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
if (lean_obj_tag(v_a_1728_) == 1)
{
lean_object* v_val_1729_; lean_object* v___x_1730_; 
v_val_1729_ = lean_ctor_get(v_a_1728_, 0);
lean_inc(v_val_1729_);
lean_dec_ref(v_a_1728_);
lean_inc_ref(v_e_1559_);
v___x_1730_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1559_, v___y_1694_, v___y_1700_, v___y_1701_, v___y_1695_, v___y_1699_, v___y_1698_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1745_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1745_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1745_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_unbox(v_a_1731_);
lean_dec(v_a_1731_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; 
lean_del_object(v___x_1733_);
lean_dec(v_val_1729_);
v___x_1736_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
v___y_1581_ = v___x_1736_;
v___y_1582_ = v___y_1694_;
v___y_1583_ = v___y_1703_;
v___y_1584_ = v___y_1696_;
v___y_1585_ = v___y_1697_;
v___y_1586_ = v___y_1700_;
v___y_1587_ = v___y_1702_;
v___y_1588_ = v___y_1701_;
v___y_1589_ = v___y_1695_;
v___y_1590_ = v___y_1699_;
v___y_1591_ = v___y_1698_;
goto v___jp_1580_;
}
else
{
lean_object* v_ctors_1737_; uint8_t v_isRec_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1743_; 
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v_ctors_1737_ = lean_ctor_get(v_val_1729_, 4);
lean_inc(v_ctors_1737_);
v_isRec_1738_ = lean_ctor_get_uint8(v_val_1729_, sizeof(void*)*6);
lean_dec(v_val_1729_);
v___x_1739_ = l_List_lengthTR___redArg(v_ctors_1737_);
lean_dec(v_ctors_1737_);
v___x_1740_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*1, v_isRec_1738_);
v___x_1741_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*1 + 1, v___x_1741_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1740_);
v___x_1743_ = v___x_1733_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1740_);
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
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_val_1729_);
lean_dec(v_a_1709_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v_a_1746_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1730_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1730_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
uint8_t v___x_1754_; 
lean_dec(v_a_1728_);
v___x_1754_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
v___y_1581_ = v___x_1754_;
v___y_1582_ = v___y_1694_;
v___y_1583_ = v___y_1703_;
v___y_1584_ = v___y_1696_;
v___y_1585_ = v___y_1697_;
v___y_1586_ = v___y_1700_;
v___y_1587_ = v___y_1702_;
v___y_1588_ = v___y_1701_;
v___y_1589_ = v___y_1695_;
v___y_1590_ = v___y_1699_;
v___y_1591_ = v___y_1698_;
goto v___jp_1580_;
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1709_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v_a_1755_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1727_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1727_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
uint8_t v___x_1763_; 
lean_dec_ref(v___x_1725_);
v___x_1763_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
v___y_1581_ = v___x_1763_;
v___y_1582_ = v___y_1694_;
v___y_1583_ = v___y_1703_;
v___y_1584_ = v___y_1696_;
v___y_1585_ = v___y_1697_;
v___y_1586_ = v___y_1700_;
v___y_1587_ = v___y_1702_;
v___y_1588_ = v___y_1701_;
v___y_1589_ = v___y_1695_;
v___y_1590_ = v___y_1699_;
v___y_1591_ = v___y_1698_;
goto v___jp_1580_;
}
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec(v_a_1709_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v___x_1764_ = lean_box(0);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1764_);
v___x_1766_ = v___x_1711_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v_a_1769_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1708_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1708_);
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
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_a_1779_; uint8_t v___x_1780_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1778_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1777_, v___y_1699_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = lean_unbox(v_a_1779_);
lean_dec(v_a_1779_);
if (v___x_1780_ == 0)
{
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
goto v___jp_1571_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Grind_updateLastTag(v___y_1694_, v___y_1703_, v___y_1696_, v___y_1697_, v___y_1700_, v___y_1702_, v___y_1701_, v___y_1695_, v___y_1699_, v___y_1698_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1703_);
lean_dec(v___y_1694_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec_ref(v___x_1781_);
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9);
v___x_1783_ = l_Lean_MessageData_ofExpr(v_e_1559_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(v___x_1777_, v___x_1784_, v___y_1701_, v___y_1695_, v___y_1699_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1701_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_dec_ref(v___x_1785_);
goto v___jp_1571_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
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
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1695_);
lean_dec_ref(v_e_1559_);
v_a_1794_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1781_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1781_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v_e_1559_);
v_a_1802_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1705_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1705_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = l_Lean_Expr_getAppNumArgs(v_e_1559_);
v___x_1812_ = lean_nat_sub(v___x_1811_, v___x_1810_);
lean_dec(v___x_1811_);
v___x_1813_ = lean_nat_sub(v___x_1812_, v___x_1810_);
lean_dec(v___x_1812_);
v___x_1814_ = l_Lean_Expr_getRevArg_x21(v_e_1559_, v___x_1813_);
lean_dec_ref(v_e_1559_);
v___x_1815_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1814_, v___y_1694_, v___y_1700_, v___y_1701_, v___y_1695_, v___y_1699_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1694_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2(lean_object* v_cls_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(v_cls_1880_, v_msg_1881_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___boxed(lean_object* v_cls_1894_, lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2(v_cls_1894_, v_msg_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1908_, lean_object* v_constName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1922_, lean_object* v_constName_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1922_, v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec(v___y_1924_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1936_, lean_object* v_ref_1937_, lean_object* v_constName_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___redArg(v_ref_1937_, v_constName_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_ref_1952_, lean_object* v_constName_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2(v_00_u03b1_1951_, v_ref_1952_, v_constName_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec(v_ref_1952_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_1966_, lean_object* v_ref_1967_, lean_object* v_msg_1968_, lean_object* v_declHint_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1967_, v_msg_1968_, v_declHint_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1982_, lean_object* v_ref_1983_, lean_object* v_msg_1984_, lean_object* v_declHint_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_1982_, v_ref_1983_, v_msg_1984_, v_declHint_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec(v_ref_1983_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_1998_, lean_object* v_declHint_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1998_, v_declHint_1999_, v___y_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2012_, lean_object* v_declHint_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_2012_, v_declHint_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
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
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2026_, lean_object* v_ref_2027_, lean_object* v_msg_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_2027_, v_msg_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_ref_2042_, lean_object* v_msg_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_2041_, v_ref_2042_, v_msg_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec(v_ref_2042_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2056_, lean_object* v_msg_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___redArg(v_msg_2057_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2070_, lean_object* v_msg_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2070_, v_msg_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2084_, lean_object* v_x_2085_){
_start:
{
if (lean_obj_tag(v_x_2085_) == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_box(0);
return v___x_2086_;
}
else
{
lean_object* v_key_2087_; lean_object* v_value_2088_; lean_object* v_tail_2089_; uint8_t v___y_2091_; lean_object* v_fst_2094_; lean_object* v_snd_2095_; lean_object* v_fst_2096_; lean_object* v_snd_2097_; uint8_t v___x_2098_; 
v_key_2087_ = lean_ctor_get(v_x_2085_, 0);
v_value_2088_ = lean_ctor_get(v_x_2085_, 1);
v_tail_2089_ = lean_ctor_get(v_x_2085_, 2);
v_fst_2094_ = lean_ctor_get(v_key_2087_, 0);
v_snd_2095_ = lean_ctor_get(v_key_2087_, 1);
v_fst_2096_ = lean_ctor_get(v_a_2084_, 0);
v_snd_2097_ = lean_ctor_get(v_a_2084_, 1);
v___x_2098_ = lean_expr_eqv(v_fst_2094_, v_fst_2096_);
if (v___x_2098_ == 0)
{
v___y_2091_ = v___x_2098_;
goto v___jp_2090_;
}
else
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_expr_eqv(v_snd_2095_, v_snd_2097_);
v___y_2091_ = v___x_2099_;
goto v___jp_2090_;
}
v___jp_2090_:
{
if (v___y_2091_ == 0)
{
v_x_2085_ = v_tail_2089_;
goto _start;
}
else
{
lean_object* v___x_2093_; 
lean_inc(v_value_2088_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_value_2088_);
return v___x_2093_;
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___f_2129_; 
v___x_2128_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2129_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2129_, 0, v___x_2128_);
return v___f_2129_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8));
v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12));
v___x_2150_ = l_Lean_stringToMessageData(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object* v___y_2151_, lean_object* v_eq_2152_, lean_object* v_a_2153_, lean_object* v_b_2154_, lean_object* v_b_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_snd_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2304_; 
v_snd_2167_ = lean_ctor_get(v_b_2155_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_b_2155_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v_b_2155_, 0);
lean_dec(v_unused_2305_);
v___x_2169_ = v_b_2155_;
v_isShared_2170_ = v_isSharedCheck_2304_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_snd_2167_);
lean_dec(v_b_2155_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2304_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_snd_2171_; lean_object* v_fst_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2303_; 
v_snd_2171_ = lean_ctor_get(v_snd_2167_, 1);
v_fst_2172_ = lean_ctor_get(v_snd_2167_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_snd_2167_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2174_ = v_snd_2167_;
v_isShared_2175_ = v_isSharedCheck_2303_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2171_);
lean_inc(v_fst_2172_);
lean_dec(v_snd_2167_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2303_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2302_; 
v_fst_2176_ = lean_ctor_get(v_snd_2171_, 0);
v_snd_2177_ = lean_ctor_get(v_snd_2171_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_snd_2171_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2179_ = v_snd_2171_;
v_isShared_2180_ = v_isSharedCheck_2302_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2177_);
lean_inc(v_fst_2176_);
lean_dec(v_snd_2171_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2302_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___y_2183_; uint8_t v___x_2196_; lean_object* v___y_2198_; uint8_t v___y_2199_; uint8_t v___y_2208_; uint8_t v___x_2300_; 
v___x_2181_ = lean_box(0);
v___x_2196_ = 1;
v___x_2300_ = l_Lean_Expr_isApp(v_fst_2176_);
if (v___x_2300_ == 0)
{
v___y_2208_ = v___x_2300_;
goto v___jp_2207_;
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = l_Lean_Expr_isApp(v_snd_2177_);
v___y_2208_ = v___x_2301_;
goto v___jp_2207_;
}
v___jp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2184_ = l_Lean_Expr_appFn_x21(v_fst_2176_);
lean_dec(v_fst_2176_);
v___x_2185_ = l_Lean_Expr_appFn_x21(v_snd_2177_);
lean_dec(v_snd_2177_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2185_);
lean_ctor_set(v___x_2179_, 0, v___x_2184_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v___x_2187_);
lean_ctor_set(v___x_2174_, 0, v___y_2183_);
v___x_2189_ = v___x_2174_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___y_2183_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2189_);
lean_ctor_set(v___x_2169_, 0, v___x_2181_);
v___x_2191_ = v___x_2169_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
v_b_2155_ = v___x_2191_;
goto _start;
}
}
}
}
v___jp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2200_ = lean_unsigned_to_nat(2u);
v___x_2201_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set_uint8(v___x_2201_, sizeof(void*)*1, v___y_2199_);
lean_ctor_set_uint8(v___x_2201_, sizeof(void*)*1 + 1, v___x_2196_);
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_fst_2176_);
lean_ctor_set(v___x_2203_, 1, v_snd_2177_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___y_2198_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2202_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
v___jp_2207_:
{
if (v___y_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_del_object(v___x_2179_);
lean_del_object(v___x_2174_);
lean_del_object(v___x_2169_);
lean_dec_ref(v_b_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_eq_2152_);
lean_dec(v___y_2151_);
v___x_2209_ = lean_unsigned_to_nat(2u);
v___x_2210_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*1, v___y_2208_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*1 + 1, v___y_2208_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_fst_2176_);
lean_ctor_set(v___x_2212_, 1, v_snd_2177_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_fst_2172_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2211_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___f_2218_; uint8_t v___x_2219_; 
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_sub(v_fst_2172_, v___x_2216_);
lean_dec(v_fst_2172_);
v___f_2218_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0);
lean_inc(v___y_2151_);
lean_inc(v___x_2217_);
v___x_2219_ = l_List_elem___redArg(v___f_2218_, v___x_2217_, v___y_2151_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_Expr_appArg_x21(v_fst_2176_);
v___x_2221_ = l_Lean_Expr_appArg_x21(v_snd_2177_);
v___x_2222_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2220_, v___x_2221_, v___y_2156_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; uint8_t v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = lean_unbox(v_a_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_del_object(v___x_2179_);
lean_del_object(v___x_2174_);
lean_del_object(v___x_2169_);
lean_dec(v___y_2151_);
v___x_2225_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1));
v___x_2226_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2225_, v___y_2164_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; uint8_t v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref(v___x_2226_);
v___x_2228_ = lean_unbox(v_a_2227_);
lean_dec(v_a_2227_);
if (v___x_2228_ == 0)
{
uint8_t v___x_2229_; 
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
lean_dec_ref(v_b_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_eq_2152_);
v___x_2229_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
v___y_2198_ = v___x_2217_;
v___y_2199_ = v___x_2229_;
goto v___jp_2197_;
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Meta_Grind_updateLastTag(v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v___x_2230_);
v___x_2231_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2152_, v___y_2156_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3);
v___x_2234_ = l_Lean_MessageData_ofExpr(v_a_2153_);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_ofExpr(v_b_2154_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = l_Lean_MessageData_ofExpr(v_eq_2152_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_MessageData_ofExpr(v___x_2220_);
v___x_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_MessageData_ofExpr(v___x_2221_);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Nat_reprFast(v_a_2232_);
v___x_2255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
v___x_2256_ = l_Lean_MessageData_ofFormat(v___x_2255_);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2253_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(v___x_2225_, v___x_2257_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2258_) == 0)
{
uint8_t v___x_2259_; 
lean_dec_ref(v___x_2258_);
v___x_2259_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
v___y_2198_ = v___x_2217_;
v___y_2199_ = v___x_2259_;
goto v___jp_2197_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2223_);
lean_dec(v___x_2217_);
lean_dec(v_snd_2177_);
lean_dec(v_fst_2176_);
v_a_2260_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2258_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2217_);
lean_dec(v_snd_2177_);
lean_dec(v_fst_2176_);
lean_dec_ref(v_b_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_eq_2152_);
v_a_2268_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2231_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2231_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2217_);
lean_dec(v_snd_2177_);
lean_dec(v_fst_2176_);
lean_dec_ref(v_b_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_eq_2152_);
v_a_2276_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2230_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2230_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2217_);
lean_dec(v_snd_2177_);
lean_dec(v_fst_2176_);
lean_dec_ref(v_b_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_eq_2152_);
v_a_2284_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2226_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2226_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_dec(v_a_2223_);
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
v___y_2183_ = v___x_2217_;
goto v___jp_2182_;
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2217_);
lean_del_object(v___x_2179_);
lean_dec(v_snd_2177_);
lean_dec(v_fst_2176_);
lean_del_object(v___x_2174_);
lean_del_object(v___x_2169_);
lean_dec_ref(v_b_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_eq_2152_);
lean_dec(v___y_2151_);
v_a_2292_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2222_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2222_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
v___y_2183_ = v___x_2217_;
goto v___jp_2182_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object* v___y_2306_, lean_object* v_eq_2307_, lean_object* v_a_2308_, lean_object* v_b_2309_, lean_object* v_b_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v___y_2306_, v_eq_2307_, v_a_2308_, v_b_2309_, v_b_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec(v___y_2311_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2323_, lean_object* v_b_2324_, lean_object* v_eq_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
uint8_t v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2370_; lean_object* v___x_2406_; 
lean_inc_ref(v_eq_2325_);
v___x_2406_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2325_, v_a_2326_, v_a_2330_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; uint8_t v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
v___x_2408_ = lean_unbox(v_a_2407_);
lean_dec(v_a_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec_ref(v___x_2406_);
lean_inc_ref(v_eq_2325_);
v___x_2409_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2325_, v_a_2326_, v_a_2330_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
v___y_2370_ = v___x_2409_;
goto v___jp_2369_;
}
else
{
v___y_2370_ = v___x_2406_;
goto v___jp_2369_;
}
}
else
{
v___y_2370_ = v___x_2406_;
goto v___jp_2369_;
}
v___jp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2340_ = l_Lean_Expr_getAppNumArgs(v_a_2323_);
v___x_2341_ = lean_box(0);
lean_inc_ref(v_b_2324_);
lean_inc_ref(v_a_2323_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_a_2323_);
lean_ctor_set(v___x_2342_, 1, v_b_2324_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2340_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2341_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v___y_2339_, v_eq_2325_, v_a_2323_, v_b_2324_, v___x_2344_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2360_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2360_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2360_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_fst_2350_; 
v_fst_2350_ = lean_ctor_get(v_a_2346_, 0);
lean_inc(v_fst_2350_);
lean_dec(v_a_2346_);
if (lean_obj_tag(v_fst_2350_) == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2351_ = lean_unsigned_to_nat(2u);
v___x_2352_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set_uint8(v___x_2352_, sizeof(void*)*1, v___y_2338_);
lean_ctor_set_uint8(v___x_2352_, sizeof(void*)*1 + 1, v___y_2338_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2352_);
v___x_2354_ = v___x_2348_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
lean_object* v_val_2356_; lean_object* v___x_2358_; 
v_val_2356_ = lean_ctor_get(v_fst_2350_, 0);
lean_inc(v_val_2356_);
lean_dec_ref(v_fst_2350_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v_val_2356_);
v___x_2358_ = v___x_2348_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_val_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2345_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2345_);
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
v___jp_2369_:
{
if (lean_obj_tag(v___y_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2397_; 
v_a_2371_ = lean_ctor_get(v___y_2370_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___y_2370_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2373_ = v___y_2370_;
v_isShared_2374_ = v_isSharedCheck_2397_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___y_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2397_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_unbox(v_a_2371_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v_toGoalState_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2373_);
v___x_2376_ = lean_st_ref_get(v_a_2326_);
v_toGoalState_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; 
v_unused_2392_ = lean_ctor_get(v___x_2376_, 1);
lean_dec(v_unused_2392_);
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_toGoalState_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_split_2381_; lean_object* v_argPosMap_2382_; lean_object* v___x_2384_; 
v_split_2381_ = lean_ctor_get(v_toGoalState_2377_, 15);
lean_inc_ref(v_split_2381_);
lean_dec_ref(v_toGoalState_2377_);
v_argPosMap_2382_ = lean_ctor_get(v_split_2381_, 6);
lean_inc_ref(v_argPosMap_2382_);
lean_dec_ref(v_split_2381_);
lean_inc_ref(v_b_2324_);
lean_inc_ref(v_a_2323_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_b_2324_);
lean_ctor_set(v___x_2379_, 0, v_a_2323_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2323_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_b_2324_);
v___x_2384_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2382_, v___x_2384_);
lean_dec_ref(v___x_2384_);
lean_dec_ref(v_argPosMap_2382_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_unbox(v_a_2371_);
lean_dec(v_a_2371_);
v___y_2338_ = v___x_2387_;
v___y_2339_ = v___x_2386_;
goto v___jp_2337_;
}
else
{
lean_object* v_val_2388_; uint8_t v___x_2389_; 
v_val_2388_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_val_2388_);
lean_dec_ref(v___x_2385_);
v___x_2389_ = lean_unbox(v_a_2371_);
lean_dec(v_a_2371_);
v___y_2338_ = v___x_2389_;
v___y_2339_ = v_val_2388_;
goto v___jp_2337_;
}
}
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec(v_a_2371_);
lean_dec_ref(v_eq_2325_);
lean_dec_ref(v_b_2324_);
lean_dec_ref(v_a_2323_);
v___x_2393_ = lean_box(0);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2393_);
v___x_2395_ = v___x_2373_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v_eq_2325_);
lean_dec_ref(v_b_2324_);
lean_dec_ref(v_a_2323_);
v_a_2398_ = lean_ctor_get(v___y_2370_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___y_2370_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___y_2370_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___y_2370_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2410_, lean_object* v_b_2411_, lean_object* v_eq_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2410_, v_b_2411_, v_eq_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec(v_a_2413_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2425_, lean_object* v_m_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2426_, v_a_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2429_, lean_object* v_m_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2429_, v_m_2430_, v_a_2431_);
lean_dec_ref(v_a_2431_);
lean_dec_ref(v_m_2430_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2433_, lean_object* v_a_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2434_, v_x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2437_, v_a_2438_, v_x_2439_);
lean_dec(v_x_2439_);
lean_dec_ref(v_a_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
uint8_t v___y_2450_; uint8_t v___y_2455_; lean_object* v___y_2456_; lean_object* v___x_2475_; 
lean_inc_ref(v_imp_2441_);
v___x_2475_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; uint8_t v___x_2477_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2475_);
v___x_2477_ = lean_unbox(v_a_2476_);
lean_dec(v_a_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2492_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2492_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2492_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_unbox(v_a_2479_);
lean_dec(v_a_2479_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = lean_box(1);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2484_);
v___x_2486_ = v___x_2481_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2488_ = lean_box(0);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2488_);
v___x_2490_ = v___x_2481_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
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
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_a_2493_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2478_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2478_);
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
else
{
lean_object* v_binderType_2501_; lean_object* v_body_2502_; lean_object* v___y_2504_; lean_object* v___x_2532_; 
v_binderType_2501_ = lean_ctor_get(v_imp_2441_, 1);
lean_inc_ref(v_binderType_2501_);
v_body_2502_ = lean_ctor_get(v_imp_2441_, 2);
lean_inc_ref(v_body_2502_);
lean_dec_ref(v_imp_2441_);
lean_inc_ref(v_binderType_2501_);
v___x_2532_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2501_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; uint8_t v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
v___x_2534_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec_ref(v___x_2532_);
v___x_2535_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2501_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
v___y_2504_ = v___x_2535_;
goto v___jp_2503_;
}
else
{
lean_dec_ref(v_binderType_2501_);
v___y_2504_ = v___x_2532_;
goto v___jp_2503_;
}
}
else
{
lean_dec_ref(v_binderType_2501_);
v___y_2504_ = v___x_2532_;
goto v___jp_2503_;
}
v___jp_2503_:
{
if (lean_obj_tag(v___y_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2523_; 
v_a_2505_ = lean_ctor_get(v___y_2504_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___y_2504_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2507_ = v___y_2504_;
v_isShared_2508_ = v_isSharedCheck_2523_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___y_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2523_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_unbox(v_a_2505_);
if (v___x_2509_ == 0)
{
uint8_t v___x_2510_; 
lean_del_object(v___x_2507_);
v___x_2510_ = l_Lean_Expr_hasLooseBVars(v_body_2502_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
lean_inc_ref(v_body_2502_);
v___x_2511_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2502_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; uint8_t v___x_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
v___x_2513_ = lean_unbox(v_a_2512_);
lean_dec(v_a_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
lean_dec_ref(v___x_2511_);
v___x_2514_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2502_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
v___x_2515_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
v___y_2455_ = v___x_2515_;
v___y_2456_ = v___x_2514_;
goto v___jp_2454_;
}
else
{
uint8_t v___x_2516_; 
lean_dec_ref(v_body_2502_);
v___x_2516_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
v___y_2455_ = v___x_2516_;
v___y_2456_ = v___x_2511_;
goto v___jp_2454_;
}
}
else
{
uint8_t v___x_2517_; 
lean_dec_ref(v_body_2502_);
v___x_2517_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
v___y_2455_ = v___x_2517_;
v___y_2456_ = v___x_2511_;
goto v___jp_2454_;
}
}
else
{
uint8_t v___x_2518_; 
lean_dec_ref(v_body_2502_);
v___x_2518_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
v___y_2450_ = v___x_2518_;
goto v___jp_2449_;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_dec(v_a_2505_);
lean_dec_ref(v_body_2502_);
v___x_2519_ = lean_box(0);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2519_);
v___x_2521_ = v___x_2507_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_body_2502_);
v_a_2524_ = lean_ctor_get(v___y_2504_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___y_2504_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___y_2504_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___y_2504_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_imp_2441_);
v_a_2536_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2475_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2475_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
v___jp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = lean_unsigned_to_nat(2u);
v___x_2452_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set_uint8(v___x_2452_, sizeof(void*)*1, v___y_2450_);
lean_ctor_set_uint8(v___x_2452_, sizeof(void*)*1 + 1, v___y_2450_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
v___jp_2454_:
{
if (lean_obj_tag(v___y_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2466_; 
v_a_2457_ = lean_ctor_get(v___y_2456_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___y_2456_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2459_ = v___y_2456_;
v_isShared_2460_ = v_isSharedCheck_2466_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___y_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2466_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_unbox(v_a_2457_);
lean_dec(v_a_2457_);
if (v___x_2461_ == 0)
{
lean_del_object(v___x_2459_);
v___y_2450_ = v___y_2455_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_box(0);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2462_);
v___x_2464_ = v___x_2459_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___y_2456_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___y_2456_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___y_2456_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___y_2456_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2553_, lean_object* v_h_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2553_, v_a_2555_, v_a_2559_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2567_, lean_object* v_h_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2567_, v_h_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec(v_a_2569_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
switch(lean_obj_tag(v_s_2581_))
{
case 0:
{
lean_object* v_e_2593_; lean_object* v___x_2594_; 
v_e_2593_ = lean_ctor_get(v_s_2581_, 0);
lean_inc_ref(v_e_2593_);
lean_dec_ref(v_s_2581_);
v___x_2594_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2593_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
return v___x_2594_;
}
case 1:
{
lean_object* v_e_2595_; lean_object* v___x_2596_; 
lean_dec(v_a_2587_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
v_e_2595_ = lean_ctor_get(v_s_2581_, 0);
lean_inc_ref(v_e_2595_);
lean_dec_ref(v_s_2581_);
v___x_2596_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2595_, v_a_2582_, v_a_2586_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2582_);
return v___x_2596_;
}
default: 
{
lean_object* v_a_2597_; lean_object* v_b_2598_; lean_object* v_eq_2599_; lean_object* v___x_2600_; 
v_a_2597_ = lean_ctor_get(v_s_2581_, 0);
lean_inc_ref(v_a_2597_);
v_b_2598_ = lean_ctor_get(v_s_2581_, 1);
lean_inc_ref(v_b_2598_);
v_eq_2599_ = lean_ctor_get(v_s_2581_, 3);
lean_inc_ref(v_eq_2599_);
lean_dec_ref(v_s_2581_);
v___x_2600_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2597_, v_b_2598_, v_eq_2599_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec(v_a_2582_);
return v___x_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* v_x_2614_){
_start:
{
if (lean_obj_tag(v_x_2614_) == 0)
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_unsigned_to_nat(1u);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* v_x_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(v_x_2617_);
lean_dec(v_x_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2619_, lean_object* v_k_2620_){
_start:
{
if (lean_obj_tag(v_t_2619_) == 0)
{
return v_k_2620_;
}
else
{
lean_object* v_c_2621_; lean_object* v_numCases_2622_; uint8_t v_isRec_2623_; uint8_t v_tryPostpone_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_c_2621_ = lean_ctor_get(v_t_2619_, 0);
lean_inc_ref(v_c_2621_);
v_numCases_2622_ = lean_ctor_get(v_t_2619_, 1);
lean_inc(v_numCases_2622_);
v_isRec_2623_ = lean_ctor_get_uint8(v_t_2619_, sizeof(void*)*2);
v_tryPostpone_2624_ = lean_ctor_get_uint8(v_t_2619_, sizeof(void*)*2 + 1);
lean_dec_ref(v_t_2619_);
v___x_2625_ = lean_box(v_isRec_2623_);
v___x_2626_ = lean_box(v_tryPostpone_2624_);
v___x_2627_ = lean_apply_4(v_k_2620_, v_c_2621_, v_numCases_2622_, v___x_2625_, v___x_2626_);
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2628_, lean_object* v_ctorIdx_2629_, lean_object* v_t_2630_, lean_object* v_h_2631_, lean_object* v_k_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2630_, v_k_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2634_, lean_object* v_ctorIdx_2635_, lean_object* v_t_2636_, lean_object* v_h_2637_, lean_object* v_k_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2634_, v_ctorIdx_2635_, v_t_2636_, v_h_2637_, v_k_2638_);
lean_dec(v_ctorIdx_2635_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2640_, lean_object* v_none_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2640_, v_none_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2643_, lean_object* v_t_2644_, lean_object* v_h_2645_, lean_object* v_none_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2644_, v_none_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2648_, lean_object* v_some_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2648_, v_some_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2651_, lean_object* v_t_2652_, lean_object* v_h_2653_, lean_object* v_some_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2652_, v_some_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2656_, lean_object* v_as_2657_, size_t v_i_2658_, size_t v_stop_2659_){
_start:
{
uint8_t v___x_2660_; 
v___x_2660_ = lean_usize_dec_eq(v_i_2658_, v_stop_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_array_uget_borrowed(v_as_2657_, v_i_2658_);
v___x_2662_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2661_, v_a_2656_);
if (v___x_2662_ == 0)
{
size_t v___x_2663_; size_t v___x_2664_; 
v___x_2663_ = ((size_t)1ULL);
v___x_2664_ = lean_usize_add(v_i_2658_, v___x_2663_);
v_i_2658_ = v___x_2664_;
goto _start;
}
else
{
return v___x_2662_;
}
}
else
{
uint8_t v___x_2666_; 
v___x_2666_ = 0;
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2667_, lean_object* v_as_2668_, lean_object* v_i_2669_, lean_object* v_stop_2670_){
_start:
{
uint64_t v_a_2842__boxed_2671_; size_t v_i_boxed_2672_; size_t v_stop_boxed_2673_; uint8_t v_res_2674_; lean_object* v_r_2675_; 
v_a_2842__boxed_2671_ = lean_unbox_uint64(v_a_2667_);
lean_dec_ref(v_a_2667_);
v_i_boxed_2672_ = lean_unbox_usize(v_i_2669_);
lean_dec(v_i_2669_);
v_stop_boxed_2673_ = lean_unbox_usize(v_stop_2670_);
lean_dec(v_stop_2670_);
v_res_2674_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2842__boxed_2671_, v_as_2668_, v_i_boxed_2672_, v_stop_boxed_2673_);
lean_dec_ref(v_as_2668_);
v_r_2675_ = lean_box(v_res_2674_);
return v_r_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2678_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2731_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2731_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2731_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
if (lean_obj_tag(v_a_2688_) == 1)
{
lean_object* v_val_2692_; lean_object* v___x_2693_; 
lean_del_object(v___x_2690_);
v_val_2692_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_val_2692_);
lean_dec_ref(v_a_2688_);
v___x_2693_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2717_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2717_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2717_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = lean_array_get_size(v_val_2692_);
v___x_2700_ = lean_nat_dec_lt(v___x_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec(v_a_2694_);
lean_dec(v_val_2692_);
v___x_2701_ = lean_box(v___x_2700_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2701_);
v___x_2703_ = v___x_2696_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
else
{
if (v___x_2700_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
lean_dec(v_a_2694_);
lean_dec(v_val_2692_);
v___x_2705_ = lean_box(v___x_2700_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2705_);
v___x_2707_ = v___x_2696_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
else
{
size_t v___x_2709_; size_t v___x_2710_; uint64_t v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2699_);
v___x_2711_ = lean_unbox_uint64(v_a_2694_);
lean_dec(v_a_2694_);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2711_, v_val_2692_, v___x_2709_, v___x_2710_);
lean_dec(v_val_2692_);
v___x_2713_ = lean_box(v___x_2712_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2713_);
v___x_2715_ = v___x_2696_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_val_2692_);
v_a_2718_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2693_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2693_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
lean_dec(v_a_2688_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
v___x_2726_ = 1;
v___x_2727_ = lean_box(v___x_2726_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2727_);
v___x_2729_ = v___x_2690_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
v_a_2732_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2687_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2687_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_c_2740_);
return v_res_2751_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2755_, lean_object* v_c_x3f_2756_, lean_object* v_cs_x27_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
if (lean_obj_tag(v_cs_2755_) == 0)
{
lean_object* v___x_2769_; lean_object* v_toGoalState_2770_; lean_object* v_split_2771_; lean_object* v_mvarId_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
v___x_2769_ = lean_st_ref_take(v_a_2758_);
v_toGoalState_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_toGoalState_2770_);
v_split_2771_ = lean_ctor_get(v_toGoalState_2770_, 15);
lean_inc_ref(v_split_2771_);
v_mvarId_2772_ = lean_ctor_get(v___x_2769_, 1);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v___x_2769_, 0);
lean_dec(v_unused_2883_);
v___x_2774_ = v___x_2769_;
v_isShared_2775_ = v_isSharedCheck_2882_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_mvarId_2772_);
lean_dec(v___x_2769_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2882_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_nextDeclIdx_2776_; lean_object* v_canon_2777_; lean_object* v_enodeMap_2778_; lean_object* v_exprs_2779_; lean_object* v_parents_2780_; lean_object* v_congrTable_2781_; lean_object* v_appMap_2782_; lean_object* v_indicesFound_2783_; lean_object* v_newFacts_2784_; uint8_t v_inconsistent_2785_; lean_object* v_nextIdx_2786_; lean_object* v_newRawFacts_2787_; lean_object* v_facts_2788_; lean_object* v_extThms_2789_; lean_object* v_ematch_2790_; lean_object* v_inj_2791_; lean_object* v_clean_2792_; lean_object* v_sstates_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2880_; 
v_nextDeclIdx_2776_ = lean_ctor_get(v_toGoalState_2770_, 0);
v_canon_2777_ = lean_ctor_get(v_toGoalState_2770_, 1);
v_enodeMap_2778_ = lean_ctor_get(v_toGoalState_2770_, 2);
v_exprs_2779_ = lean_ctor_get(v_toGoalState_2770_, 3);
v_parents_2780_ = lean_ctor_get(v_toGoalState_2770_, 4);
v_congrTable_2781_ = lean_ctor_get(v_toGoalState_2770_, 5);
v_appMap_2782_ = lean_ctor_get(v_toGoalState_2770_, 6);
v_indicesFound_2783_ = lean_ctor_get(v_toGoalState_2770_, 7);
v_newFacts_2784_ = lean_ctor_get(v_toGoalState_2770_, 8);
v_inconsistent_2785_ = lean_ctor_get_uint8(v_toGoalState_2770_, sizeof(void*)*18);
v_nextIdx_2786_ = lean_ctor_get(v_toGoalState_2770_, 9);
v_newRawFacts_2787_ = lean_ctor_get(v_toGoalState_2770_, 10);
v_facts_2788_ = lean_ctor_get(v_toGoalState_2770_, 11);
v_extThms_2789_ = lean_ctor_get(v_toGoalState_2770_, 12);
v_ematch_2790_ = lean_ctor_get(v_toGoalState_2770_, 13);
v_inj_2791_ = lean_ctor_get(v_toGoalState_2770_, 14);
v_clean_2792_ = lean_ctor_get(v_toGoalState_2770_, 16);
v_sstates_2793_ = lean_ctor_get(v_toGoalState_2770_, 17);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_toGoalState_2770_);
if (v_isSharedCheck_2880_ == 0)
{
lean_object* v_unused_2881_; 
v_unused_2881_ = lean_ctor_get(v_toGoalState_2770_, 15);
lean_dec(v_unused_2881_);
v___x_2795_ = v_toGoalState_2770_;
v_isShared_2796_ = v_isSharedCheck_2880_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_sstates_2793_);
lean_inc(v_clean_2792_);
lean_inc(v_inj_2791_);
lean_inc(v_ematch_2790_);
lean_inc(v_extThms_2789_);
lean_inc(v_facts_2788_);
lean_inc(v_newRawFacts_2787_);
lean_inc(v_nextIdx_2786_);
lean_inc(v_newFacts_2784_);
lean_inc(v_indicesFound_2783_);
lean_inc(v_appMap_2782_);
lean_inc(v_congrTable_2781_);
lean_inc(v_parents_2780_);
lean_inc(v_exprs_2779_);
lean_inc(v_enodeMap_2778_);
lean_inc(v_canon_2777_);
lean_inc(v_nextDeclIdx_2776_);
lean_dec(v_toGoalState_2770_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2880_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v_num_2797_; lean_object* v_added_2798_; lean_object* v_resolved_2799_; lean_object* v_trace_2800_; lean_object* v_lookaheads_2801_; lean_object* v_argPosMap_2802_; lean_object* v_argsAt_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2878_; 
v_num_2797_ = lean_ctor_get(v_split_2771_, 0);
v_added_2798_ = lean_ctor_get(v_split_2771_, 2);
v_resolved_2799_ = lean_ctor_get(v_split_2771_, 3);
v_trace_2800_ = lean_ctor_get(v_split_2771_, 4);
v_lookaheads_2801_ = lean_ctor_get(v_split_2771_, 5);
v_argPosMap_2802_ = lean_ctor_get(v_split_2771_, 6);
v_argsAt_2803_ = lean_ctor_get(v_split_2771_, 7);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_split_2771_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v_split_2771_, 1);
lean_dec(v_unused_2879_);
v___x_2805_ = v_split_2771_;
v_isShared_2806_ = v_isSharedCheck_2878_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_argsAt_2803_);
lean_inc(v_argPosMap_2802_);
lean_inc(v_lookaheads_2801_);
lean_inc(v_trace_2800_);
lean_inc(v_resolved_2799_);
lean_inc(v_added_2798_);
lean_inc(v_num_2797_);
lean_dec(v_split_2771_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2878_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = l_List_reverse___redArg(v_cs_x27_2757_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 1, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_num_2797_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_added_2798_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_resolved_2799_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_trace_2800_);
lean_ctor_set(v_reuseFailAlloc_2877_, 5, v_lookaheads_2801_);
lean_ctor_set(v_reuseFailAlloc_2877_, 6, v_argPosMap_2802_);
lean_ctor_set(v_reuseFailAlloc_2877_, 7, v_argsAt_2803_);
v___x_2809_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2811_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 15, v___x_2809_);
v___x_2811_ = v___x_2795_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_nextDeclIdx_2776_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_canon_2777_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_enodeMap_2778_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_exprs_2779_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_parents_2780_);
lean_ctor_set(v_reuseFailAlloc_2876_, 5, v_congrTable_2781_);
lean_ctor_set(v_reuseFailAlloc_2876_, 6, v_appMap_2782_);
lean_ctor_set(v_reuseFailAlloc_2876_, 7, v_indicesFound_2783_);
lean_ctor_set(v_reuseFailAlloc_2876_, 8, v_newFacts_2784_);
lean_ctor_set(v_reuseFailAlloc_2876_, 9, v_nextIdx_2786_);
lean_ctor_set(v_reuseFailAlloc_2876_, 10, v_newRawFacts_2787_);
lean_ctor_set(v_reuseFailAlloc_2876_, 11, v_facts_2788_);
lean_ctor_set(v_reuseFailAlloc_2876_, 12, v_extThms_2789_);
lean_ctor_set(v_reuseFailAlloc_2876_, 13, v_ematch_2790_);
lean_ctor_set(v_reuseFailAlloc_2876_, 14, v_inj_2791_);
lean_ctor_set(v_reuseFailAlloc_2876_, 15, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2876_, 16, v_clean_2792_);
lean_ctor_set(v_reuseFailAlloc_2876_, 17, v_sstates_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*18, v_inconsistent_2785_);
v___x_2811_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2811_);
v___x_2813_ = v___x_2774_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_mvarId_2772_);
v___x_2813_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_st_ref_set(v_a_2758_, v___x_2813_);
if (lean_obj_tag(v_c_x3f_2756_) == 1)
{
lean_object* v___x_2815_; lean_object* v_toGoalState_2816_; lean_object* v_ematch_2817_; lean_object* v_mvarId_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2872_; 
v___x_2815_ = lean_st_ref_take(v_a_2758_);
v_toGoalState_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc_ref(v_toGoalState_2816_);
v_ematch_2817_ = lean_ctor_get(v_toGoalState_2816_, 13);
lean_inc_ref(v_ematch_2817_);
v_mvarId_2818_ = lean_ctor_get(v___x_2815_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2873_);
v___x_2820_ = v___x_2815_;
v_isShared_2821_ = v_isSharedCheck_2872_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_mvarId_2818_);
lean_dec(v___x_2815_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2872_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_nextDeclIdx_2822_; lean_object* v_canon_2823_; lean_object* v_enodeMap_2824_; lean_object* v_exprs_2825_; lean_object* v_parents_2826_; lean_object* v_congrTable_2827_; lean_object* v_appMap_2828_; lean_object* v_indicesFound_2829_; lean_object* v_newFacts_2830_; uint8_t v_inconsistent_2831_; lean_object* v_nextIdx_2832_; lean_object* v_newRawFacts_2833_; lean_object* v_facts_2834_; lean_object* v_extThms_2835_; lean_object* v_inj_2836_; lean_object* v_split_2837_; lean_object* v_clean_2838_; lean_object* v_sstates_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2870_; 
v_nextDeclIdx_2822_ = lean_ctor_get(v_toGoalState_2816_, 0);
v_canon_2823_ = lean_ctor_get(v_toGoalState_2816_, 1);
v_enodeMap_2824_ = lean_ctor_get(v_toGoalState_2816_, 2);
v_exprs_2825_ = lean_ctor_get(v_toGoalState_2816_, 3);
v_parents_2826_ = lean_ctor_get(v_toGoalState_2816_, 4);
v_congrTable_2827_ = lean_ctor_get(v_toGoalState_2816_, 5);
v_appMap_2828_ = lean_ctor_get(v_toGoalState_2816_, 6);
v_indicesFound_2829_ = lean_ctor_get(v_toGoalState_2816_, 7);
v_newFacts_2830_ = lean_ctor_get(v_toGoalState_2816_, 8);
v_inconsistent_2831_ = lean_ctor_get_uint8(v_toGoalState_2816_, sizeof(void*)*18);
v_nextIdx_2832_ = lean_ctor_get(v_toGoalState_2816_, 9);
v_newRawFacts_2833_ = lean_ctor_get(v_toGoalState_2816_, 10);
v_facts_2834_ = lean_ctor_get(v_toGoalState_2816_, 11);
v_extThms_2835_ = lean_ctor_get(v_toGoalState_2816_, 12);
v_inj_2836_ = lean_ctor_get(v_toGoalState_2816_, 14);
v_split_2837_ = lean_ctor_get(v_toGoalState_2816_, 15);
v_clean_2838_ = lean_ctor_get(v_toGoalState_2816_, 16);
v_sstates_2839_ = lean_ctor_get(v_toGoalState_2816_, 17);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_toGoalState_2816_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v_toGoalState_2816_, 13);
lean_dec(v_unused_2871_);
v___x_2841_ = v_toGoalState_2816_;
v_isShared_2842_ = v_isSharedCheck_2870_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_sstates_2839_);
lean_inc(v_clean_2838_);
lean_inc(v_split_2837_);
lean_inc(v_inj_2836_);
lean_inc(v_extThms_2835_);
lean_inc(v_facts_2834_);
lean_inc(v_newRawFacts_2833_);
lean_inc(v_nextIdx_2832_);
lean_inc(v_newFacts_2830_);
lean_inc(v_indicesFound_2829_);
lean_inc(v_appMap_2828_);
lean_inc(v_congrTable_2827_);
lean_inc(v_parents_2826_);
lean_inc(v_exprs_2825_);
lean_inc(v_enodeMap_2824_);
lean_inc(v_canon_2823_);
lean_inc(v_nextDeclIdx_2822_);
lean_dec(v_toGoalState_2816_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2870_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_thmMap_2843_; lean_object* v_gmt_2844_; lean_object* v_thms_2845_; lean_object* v_newThms_2846_; lean_object* v_numInstances_2847_; lean_object* v_numDelayedInstances_2848_; lean_object* v_preInstances_2849_; lean_object* v_nextThmIdx_2850_; lean_object* v_matchEqNames_2851_; lean_object* v_delayedThmInsts_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2868_; 
v_thmMap_2843_ = lean_ctor_get(v_ematch_2817_, 0);
v_gmt_2844_ = lean_ctor_get(v_ematch_2817_, 1);
v_thms_2845_ = lean_ctor_get(v_ematch_2817_, 2);
v_newThms_2846_ = lean_ctor_get(v_ematch_2817_, 3);
v_numInstances_2847_ = lean_ctor_get(v_ematch_2817_, 4);
v_numDelayedInstances_2848_ = lean_ctor_get(v_ematch_2817_, 5);
v_preInstances_2849_ = lean_ctor_get(v_ematch_2817_, 7);
v_nextThmIdx_2850_ = lean_ctor_get(v_ematch_2817_, 8);
v_matchEqNames_2851_ = lean_ctor_get(v_ematch_2817_, 9);
v_delayedThmInsts_2852_ = lean_ctor_get(v_ematch_2817_, 10);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_ematch_2817_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v_ematch_2817_, 6);
lean_dec(v_unused_2869_);
v___x_2854_ = v_ematch_2817_;
v_isShared_2855_ = v_isSharedCheck_2868_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_delayedThmInsts_2852_);
lean_inc(v_matchEqNames_2851_);
lean_inc(v_nextThmIdx_2850_);
lean_inc(v_preInstances_2849_);
lean_inc(v_numDelayedInstances_2848_);
lean_inc(v_numInstances_2847_);
lean_inc(v_newThms_2846_);
lean_inc(v_thms_2845_);
lean_inc(v_gmt_2844_);
lean_inc(v_thmMap_2843_);
lean_dec(v_ematch_2817_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2868_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
v___x_2856_ = lean_unsigned_to_nat(0u);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 6, v___x_2856_);
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_thmMap_2843_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_gmt_2844_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_thms_2845_);
lean_ctor_set(v_reuseFailAlloc_2867_, 3, v_newThms_2846_);
lean_ctor_set(v_reuseFailAlloc_2867_, 4, v_numInstances_2847_);
lean_ctor_set(v_reuseFailAlloc_2867_, 5, v_numDelayedInstances_2848_);
lean_ctor_set(v_reuseFailAlloc_2867_, 6, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2867_, 7, v_preInstances_2849_);
lean_ctor_set(v_reuseFailAlloc_2867_, 8, v_nextThmIdx_2850_);
lean_ctor_set(v_reuseFailAlloc_2867_, 9, v_matchEqNames_2851_);
lean_ctor_set(v_reuseFailAlloc_2867_, 10, v_delayedThmInsts_2852_);
v___x_2858_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2860_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 13, v___x_2858_);
v___x_2860_ = v___x_2841_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_nextDeclIdx_2822_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_canon_2823_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_enodeMap_2824_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_exprs_2825_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v_parents_2826_);
lean_ctor_set(v_reuseFailAlloc_2866_, 5, v_congrTable_2827_);
lean_ctor_set(v_reuseFailAlloc_2866_, 6, v_appMap_2828_);
lean_ctor_set(v_reuseFailAlloc_2866_, 7, v_indicesFound_2829_);
lean_ctor_set(v_reuseFailAlloc_2866_, 8, v_newFacts_2830_);
lean_ctor_set(v_reuseFailAlloc_2866_, 9, v_nextIdx_2832_);
lean_ctor_set(v_reuseFailAlloc_2866_, 10, v_newRawFacts_2833_);
lean_ctor_set(v_reuseFailAlloc_2866_, 11, v_facts_2834_);
lean_ctor_set(v_reuseFailAlloc_2866_, 12, v_extThms_2835_);
lean_ctor_set(v_reuseFailAlloc_2866_, 13, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2866_, 14, v_inj_2836_);
lean_ctor_set(v_reuseFailAlloc_2866_, 15, v_split_2837_);
lean_ctor_set(v_reuseFailAlloc_2866_, 16, v_clean_2838_);
lean_ctor_set(v_reuseFailAlloc_2866_, 17, v_sstates_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2866_, sizeof(void*)*18, v_inconsistent_2831_);
v___x_2860_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2860_);
v___x_2862_ = v___x_2820_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_mvarId_2818_);
v___x_2862_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_st_ref_set(v_a_2758_, v___x_2862_);
lean_dec(v_a_2758_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_c_x3f_2756_);
return v___x_2864_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_a_2758_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_c_x3f_2756_);
return v___x_2874_;
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
lean_object* v_head_2884_; lean_object* v_tail_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_3103_; 
v_head_2884_ = lean_ctor_get(v_cs_2755_, 0);
v_tail_2885_ = lean_ctor_get(v_cs_2755_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_cs_2755_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_2887_ = v_cs_2755_;
v_isShared_2888_ = v_isSharedCheck_3103_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_tail_2885_);
lean_inc(v_head_2884_);
lean_dec(v_cs_2755_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_3103_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; uint8_t v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint8_t v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; uint8_t v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2961_; lean_object* v___y_2962_; uint8_t v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; uint8_t v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; uint8_t v___y_2976_; lean_object* v___y_2980_; lean_object* v___y_2981_; uint8_t v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; uint8_t v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; uint8_t v___y_2995_; lean_object* v___y_2999_; uint8_t v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; uint8_t v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; uint8_t v___y_3012_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___x_3065_; 
lean_inc(v_a_2767_);
lean_inc_ref(v_a_2766_);
lean_inc(v_a_2765_);
lean_inc_ref(v_a_2764_);
v___x_3065_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2884_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; uint8_t v___x_3067_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref(v___x_3065_);
v___x_3067_ = lean_unbox(v_a_3066_);
lean_dec(v_a_3066_);
if (v___x_3067_ == 0)
{
lean_del_object(v___x_2887_);
lean_dec(v_head_2884_);
v_cs_2755_ = v_tail_2885_;
goto _start;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v_a_3071_; uint8_t v___x_3072_; 
v___x_3069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3070_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3069_, v_a_2766_);
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = lean_unbox(v_a_3071_);
lean_dec(v_a_3071_);
if (v___x_3072_ == 0)
{
v___y_3023_ = v_a_2758_;
v___y_3024_ = v_a_2759_;
v___y_3025_ = v_a_2760_;
v___y_3026_ = v_a_2761_;
v___y_3027_ = v_a_2762_;
v___y_3028_ = v_a_2763_;
v___y_3029_ = v_a_2764_;
v___y_3030_ = v_a_2765_;
v___y_3031_ = v_a_2766_;
v___y_3032_ = v_a_2767_;
goto v___jp_3022_;
}
else
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_Meta_Grind_updateLastTag(v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec_ref(v___x_3073_);
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3075_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2884_);
v___x_3076_ = l_Lean_MessageData_ofExpr(v___x_3075_);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3074_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(v___x_3069_, v___x_3077_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref(v___x_3078_);
v___y_3023_ = v_a_2758_;
v___y_3024_ = v_a_2759_;
v___y_3025_ = v_a_2760_;
v___y_3026_ = v_a_2761_;
v___y_3027_ = v_a_2762_;
v___y_3028_ = v_a_2763_;
v___y_3029_ = v_a_2764_;
v___y_3030_ = v_a_2765_;
v___y_3031_ = v_a_2766_;
v___y_3032_ = v_a_2767_;
goto v___jp_3022_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_3087_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3073_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3073_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_3095_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3065_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3065_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
v___jp_2889_:
{
lean_object* v___x_2901_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v_cs_x27_2757_);
v___x_2901_ = v___x_2887_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_head_2884_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_cs_x27_2757_);
v___x_2901_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v_cs_2755_ = v_tail_2885_;
v_cs_x27_2757_ = v___x_2901_;
v_a_2758_ = v___y_2891_;
v_a_2759_ = v___y_2899_;
v_a_2760_ = v___y_2892_;
v_a_2761_ = v___y_2895_;
v_a_2762_ = v___y_2890_;
v_a_2763_ = v___y_2896_;
v_a_2764_ = v___y_2898_;
v_a_2765_ = v___y_2897_;
v_a_2766_ = v___y_2894_;
v_a_2767_ = v___y_2893_;
goto _start;
}
}
v___jp_2904_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2919_, 0, v_head_2884_);
lean_ctor_set(v___x_2919_, 1, v___y_2908_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*2, v___y_2907_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*2 + 1, v___y_2914_);
v___x_2920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___y_2905_);
lean_ctor_set(v___x_2920_, 1, v_cs_x27_2757_);
v_cs_2755_ = v_tail_2885_;
v_c_x3f_2756_ = v___x_2919_;
v_cs_x27_2757_ = v___x_2920_;
v_a_2758_ = v___y_2909_;
v_a_2759_ = v___y_2918_;
v_a_2760_ = v___y_2910_;
v_a_2761_ = v___y_2911_;
v_a_2762_ = v___y_2906_;
v_a_2763_ = v___y_2916_;
v_a_2764_ = v___y_2913_;
v_a_2765_ = v___y_2917_;
v_a_2766_ = v___y_2912_;
v_a_2767_ = v___y_2915_;
goto _start;
}
v___jp_2922_:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2884_, v___y_2927_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_2923_, v___y_2927_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; uint8_t v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = lean_nat_dec_lt(v_a_2939_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec(v_a_2939_);
if (v___x_2942_ == 0)
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_nat_dec_lt(v___y_2926_, v___y_2933_);
lean_dec(v___y_2933_);
if (v___x_2943_ == 0)
{
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2923_);
v___y_2890_ = v___y_2924_;
v___y_2891_ = v___y_2927_;
v___y_2892_ = v___y_2928_;
v___y_2893_ = v___y_2934_;
v___y_2894_ = v___y_2929_;
v___y_2895_ = v___y_2930_;
v___y_2896_ = v___y_2935_;
v___y_2897_ = v___y_2936_;
v___y_2898_ = v___y_2931_;
v___y_2899_ = v___y_2937_;
goto v___jp_2889_;
}
else
{
lean_del_object(v___x_2887_);
lean_dec(v_c_x3f_2756_);
v___y_2905_ = v___y_2923_;
v___y_2906_ = v___y_2924_;
v___y_2907_ = v___y_2925_;
v___y_2908_ = v___y_2926_;
v___y_2909_ = v___y_2927_;
v___y_2910_ = v___y_2928_;
v___y_2911_ = v___y_2930_;
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2931_;
v___y_2914_ = v___y_2932_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
goto v___jp_2904_;
}
}
else
{
lean_dec(v___y_2933_);
lean_del_object(v___x_2887_);
lean_dec(v_c_x3f_2756_);
v___y_2905_ = v___y_2923_;
v___y_2906_ = v___y_2924_;
v___y_2907_ = v___y_2925_;
v___y_2908_ = v___y_2926_;
v___y_2909_ = v___y_2927_;
v___y_2910_ = v___y_2928_;
v___y_2911_ = v___y_2930_;
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2931_;
v___y_2914_ = v___y_2932_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
goto v___jp_2904_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec(v_a_2939_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_2944_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2940_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2940_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_2952_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2938_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2938_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2960_:
{
if (v___y_2976_ == 0)
{
v___y_2923_ = v___y_2961_;
v___y_2924_ = v___y_2962_;
v___y_2925_ = v___y_2963_;
v___y_2926_ = v___y_2964_;
v___y_2927_ = v___y_2965_;
v___y_2928_ = v___y_2966_;
v___y_2929_ = v___y_2967_;
v___y_2930_ = v___y_2968_;
v___y_2931_ = v___y_2969_;
v___y_2932_ = v___y_2970_;
v___y_2933_ = v___y_2971_;
v___y_2934_ = v___y_2972_;
v___y_2935_ = v___y_2973_;
v___y_2936_ = v___y_2974_;
v___y_2937_ = v___y_2975_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = lean_nat_dec_lt(v___x_2977_, v___y_2971_);
if (v___x_2978_ == 0)
{
v___y_2923_ = v___y_2961_;
v___y_2924_ = v___y_2962_;
v___y_2925_ = v___y_2963_;
v___y_2926_ = v___y_2964_;
v___y_2927_ = v___y_2965_;
v___y_2928_ = v___y_2966_;
v___y_2929_ = v___y_2967_;
v___y_2930_ = v___y_2968_;
v___y_2931_ = v___y_2969_;
v___y_2932_ = v___y_2970_;
v___y_2933_ = v___y_2971_;
v___y_2934_ = v___y_2972_;
v___y_2935_ = v___y_2973_;
v___y_2936_ = v___y_2974_;
v___y_2937_ = v___y_2975_;
goto v___jp_2922_;
}
else
{
lean_dec(v___y_2971_);
lean_del_object(v___x_2887_);
lean_dec(v_c_x3f_2756_);
v___y_2905_ = v___y_2961_;
v___y_2906_ = v___y_2962_;
v___y_2907_ = v___y_2963_;
v___y_2908_ = v___y_2964_;
v___y_2909_ = v___y_2965_;
v___y_2910_ = v___y_2966_;
v___y_2911_ = v___y_2968_;
v___y_2912_ = v___y_2967_;
v___y_2913_ = v___y_2969_;
v___y_2914_ = v___y_2970_;
v___y_2915_ = v___y_2972_;
v___y_2916_ = v___y_2973_;
v___y_2917_ = v___y_2974_;
v___y_2918_ = v___y_2975_;
goto v___jp_2904_;
}
}
}
v___jp_2979_:
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = lean_unsigned_to_nat(1u);
v___x_2997_ = lean_nat_dec_eq(v___y_2983_, v___x_2996_);
if (v___x_2997_ == 0)
{
v___y_2961_ = v___y_2980_;
v___y_2962_ = v___y_2981_;
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2983_;
v___y_2965_ = v___y_2984_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2986_;
v___y_2968_ = v___y_2987_;
v___y_2969_ = v___y_2988_;
v___y_2970_ = v___y_2989_;
v___y_2971_ = v___y_2990_;
v___y_2972_ = v___y_2991_;
v___y_2973_ = v___y_2992_;
v___y_2974_ = v___y_2993_;
v___y_2975_ = v___y_2994_;
v___y_2976_ = v___x_2997_;
goto v___jp_2960_;
}
else
{
if (v___y_2982_ == 0)
{
v___y_2961_ = v___y_2980_;
v___y_2962_ = v___y_2981_;
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2983_;
v___y_2965_ = v___y_2984_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2986_;
v___y_2968_ = v___y_2987_;
v___y_2969_ = v___y_2988_;
v___y_2970_ = v___y_2989_;
v___y_2971_ = v___y_2990_;
v___y_2972_ = v___y_2991_;
v___y_2973_ = v___y_2992_;
v___y_2974_ = v___y_2993_;
v___y_2975_ = v___y_2994_;
v___y_2976_ = v___x_2997_;
goto v___jp_2960_;
}
else
{
v___y_2961_ = v___y_2980_;
v___y_2962_ = v___y_2981_;
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2983_;
v___y_2965_ = v___y_2984_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2986_;
v___y_2968_ = v___y_2987_;
v___y_2969_ = v___y_2988_;
v___y_2970_ = v___y_2989_;
v___y_2971_ = v___y_2990_;
v___y_2972_ = v___y_2991_;
v___y_2973_ = v___y_2992_;
v___y_2974_ = v___y_2993_;
v___y_2975_ = v___y_2994_;
v___y_2976_ = v___y_2995_;
goto v___jp_2960_;
}
}
}
v___jp_2998_:
{
if (lean_obj_tag(v_c_x3f_2756_) == 0)
{
lean_object* v___x_3013_; 
lean_del_object(v___x_2887_);
v___x_3013_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3013_, 0, v_head_2884_);
lean_ctor_set(v___x_3013_, 1, v___y_3001_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*2, v___y_3000_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*2 + 1, v___y_3007_);
v_cs_2755_ = v_tail_2885_;
v_c_x3f_2756_ = v___x_3013_;
v_a_2758_ = v___y_3002_;
v_a_2759_ = v___y_3011_;
v_a_2760_ = v___y_3003_;
v_a_2761_ = v___y_3004_;
v_a_2762_ = v___y_2999_;
v_a_2763_ = v___y_3009_;
v_a_2764_ = v___y_3006_;
v_a_2765_ = v___y_3010_;
v_a_2766_ = v___y_3005_;
v_a_2767_ = v___y_3008_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3015_; 
v_tryPostpone_3015_ = lean_ctor_get_uint8(v_c_x3f_2756_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3015_ == 0)
{
if (v___y_3007_ == 0)
{
lean_object* v_c_3016_; lean_object* v_numCases_3017_; 
v_c_3016_ = lean_ctor_get(v_c_x3f_2756_, 0);
v_numCases_3017_ = lean_ctor_get(v_c_x3f_2756_, 1);
lean_inc(v_numCases_3017_);
lean_inc_ref(v_c_3016_);
v___y_2980_ = v_c_3016_;
v___y_2981_ = v___y_2999_;
v___y_2982_ = v___y_3000_;
v___y_2983_ = v___y_3001_;
v___y_2984_ = v___y_3002_;
v___y_2985_ = v___y_3003_;
v___y_2986_ = v___y_3005_;
v___y_2987_ = v___y_3004_;
v___y_2988_ = v___y_3006_;
v___y_2989_ = v___y_3007_;
v___y_2990_ = v_numCases_3017_;
v___y_2991_ = v___y_3008_;
v___y_2992_ = v___y_3009_;
v___y_2993_ = v___y_3010_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___y_3007_;
goto v___jp_2979_;
}
else
{
lean_dec(v___y_3001_);
v___y_2890_ = v___y_2999_;
v___y_2891_ = v___y_3002_;
v___y_2892_ = v___y_3003_;
v___y_2893_ = v___y_3008_;
v___y_2894_ = v___y_3005_;
v___y_2895_ = v___y_3004_;
v___y_2896_ = v___y_3009_;
v___y_2897_ = v___y_3010_;
v___y_2898_ = v___y_3006_;
v___y_2899_ = v___y_3011_;
goto v___jp_2889_;
}
}
else
{
if (v___y_3007_ == 0)
{
lean_object* v_c_3018_; 
lean_del_object(v___x_2887_);
v_c_3018_ = lean_ctor_get(v_c_x3f_2756_, 0);
lean_inc_ref(v_c_3018_);
lean_dec_ref(v_c_x3f_2756_);
v___y_2905_ = v_c_3018_;
v___y_2906_ = v___y_2999_;
v___y_2907_ = v___y_3000_;
v___y_2908_ = v___y_3001_;
v___y_2909_ = v___y_3002_;
v___y_2910_ = v___y_3003_;
v___y_2911_ = v___y_3004_;
v___y_2912_ = v___y_3005_;
v___y_2913_ = v___y_3006_;
v___y_2914_ = v___y_3007_;
v___y_2915_ = v___y_3008_;
v___y_2916_ = v___y_3009_;
v___y_2917_ = v___y_3010_;
v___y_2918_ = v___y_3011_;
goto v___jp_2904_;
}
else
{
if (v___y_3012_ == 0)
{
lean_object* v_c_3019_; lean_object* v_numCases_3020_; 
v_c_3019_ = lean_ctor_get(v_c_x3f_2756_, 0);
v_numCases_3020_ = lean_ctor_get(v_c_x3f_2756_, 1);
lean_inc(v_numCases_3020_);
lean_inc_ref(v_c_3019_);
v___y_2980_ = v_c_3019_;
v___y_2981_ = v___y_2999_;
v___y_2982_ = v___y_3000_;
v___y_2983_ = v___y_3001_;
v___y_2984_ = v___y_3002_;
v___y_2985_ = v___y_3003_;
v___y_2986_ = v___y_3005_;
v___y_2987_ = v___y_3004_;
v___y_2988_ = v___y_3006_;
v___y_2989_ = v___y_3007_;
v___y_2990_ = v_numCases_3020_;
v___y_2991_ = v___y_3008_;
v___y_2992_ = v___y_3009_;
v___y_2993_ = v___y_3010_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___y_3012_;
goto v___jp_2979_;
}
else
{
lean_object* v_c_3021_; 
lean_del_object(v___x_2887_);
v_c_3021_ = lean_ctor_get(v_c_x3f_2756_, 0);
lean_inc_ref(v_c_3021_);
lean_dec_ref(v_c_x3f_2756_);
v___y_2905_ = v_c_3021_;
v___y_2906_ = v___y_2999_;
v___y_2907_ = v___y_3000_;
v___y_2908_ = v___y_3001_;
v___y_2909_ = v___y_3002_;
v___y_2910_ = v___y_3003_;
v___y_2911_ = v___y_3004_;
v___y_2912_ = v___y_3005_;
v___y_2913_ = v___y_3006_;
v___y_2914_ = v___y_3007_;
v___y_2915_ = v___y_3008_;
v___y_2916_ = v___y_3009_;
v___y_2917_ = v___y_3010_;
v___y_2918_ = v___y_3011_;
goto v___jp_2904_;
}
}
}
}
}
v___jp_3022_:
{
lean_object* v___x_3033_; 
lean_inc(v___y_3032_);
lean_inc_ref(v___y_3031_);
lean_inc(v___y_3030_);
lean_inc_ref(v___y_3029_);
lean_inc(v___y_3028_);
lean_inc_ref(v___y_3027_);
lean_inc(v___y_3026_);
lean_inc_ref(v___y_3025_);
lean_inc(v___y_3024_);
lean_inc(v___y_3023_);
lean_inc(v_head_2884_);
v___x_3033_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2884_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
switch(lean_obj_tag(v_a_3034_))
{
case 0:
{
lean_del_object(v___x_2887_);
lean_dec(v_head_2884_);
v_cs_2755_ = v_tail_2885_;
v_a_2758_ = v___y_3023_;
v_a_2759_ = v___y_3024_;
v_a_2760_ = v___y_3025_;
v_a_2761_ = v___y_3026_;
v_a_2762_ = v___y_3027_;
v_a_2763_ = v___y_3028_;
v_a_2764_ = v___y_3029_;
v_a_2765_ = v___y_3030_;
v_a_2766_ = v___y_3031_;
v_a_2767_ = v___y_3032_;
goto _start;
}
case 1:
{
lean_object* v___x_3036_; 
lean_del_object(v___x_2887_);
v___x_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_head_2884_);
lean_ctor_set(v___x_3036_, 1, v_cs_x27_2757_);
v_cs_2755_ = v_tail_2885_;
v_cs_x27_2757_ = v___x_3036_;
v_a_2758_ = v___y_3023_;
v_a_2759_ = v___y_3024_;
v_a_2760_ = v___y_3025_;
v_a_2761_ = v___y_3026_;
v_a_2762_ = v___y_3027_;
v_a_2763_ = v___y_3028_;
v_a_2764_ = v___y_3029_;
v_a_2765_ = v___y_3030_;
v_a_2766_ = v___y_3031_;
v_a_2767_ = v___y_3032_;
goto _start;
}
default: 
{
lean_object* v_numCases_3038_; uint8_t v_isRec_3039_; uint8_t v_tryPostpone_3040_; lean_object* v___x_3041_; 
v_numCases_3038_ = lean_ctor_get(v_a_3034_, 0);
lean_inc(v_numCases_3038_);
v_isRec_3039_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*1);
v_tryPostpone_3040_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*1 + 1);
lean_dec_ref(v_a_3034_);
v___x_3041_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3025_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; uint8_t v___x_3043_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v___x_3041_);
v___x_3043_ = lean_unbox(v_a_3042_);
if (v___x_3043_ == 0)
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_unbox(v_a_3042_);
lean_dec(v_a_3042_);
v___y_2999_ = v___y_3027_;
v___y_3000_ = v_isRec_3039_;
v___y_3001_ = v_numCases_3038_;
v___y_3002_ = v___y_3023_;
v___y_3003_ = v___y_3025_;
v___y_3004_ = v___y_3026_;
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___y_3029_;
v___y_3007_ = v_tryPostpone_3040_;
v___y_3008_ = v___y_3032_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3030_;
v___y_3011_ = v___y_3024_;
v___y_3012_ = v___x_3044_;
goto v___jp_2998_;
}
else
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
lean_dec(v_a_3042_);
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_dec_lt(v___x_3045_, v_numCases_3038_);
if (v___x_3046_ == 0)
{
v___y_2999_ = v___y_3027_;
v___y_3000_ = v_isRec_3039_;
v___y_3001_ = v_numCases_3038_;
v___y_3002_ = v___y_3023_;
v___y_3003_ = v___y_3025_;
v___y_3004_ = v___y_3026_;
v___y_3005_ = v___y_3031_;
v___y_3006_ = v___y_3029_;
v___y_3007_ = v_tryPostpone_3040_;
v___y_3008_ = v___y_3032_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3030_;
v___y_3011_ = v___y_3024_;
v___y_3012_ = v___x_3046_;
goto v___jp_2998_;
}
else
{
lean_object* v___x_3047_; 
lean_dec(v_numCases_3038_);
lean_del_object(v___x_2887_);
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v_head_2884_);
lean_ctor_set(v___x_3047_, 1, v_cs_x27_2757_);
v_cs_2755_ = v_tail_2885_;
v_cs_x27_2757_ = v___x_3047_;
v_a_2758_ = v___y_3023_;
v_a_2759_ = v___y_3024_;
v_a_2760_ = v___y_3025_;
v_a_2761_ = v___y_3026_;
v_a_2762_ = v___y_3027_;
v_a_2763_ = v___y_3028_;
v_a_2764_ = v___y_3029_;
v_a_2765_ = v___y_3030_;
v_a_2766_ = v___y_3031_;
v_a_2767_ = v___y_3032_;
goto _start;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_numCases_3038_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3023_);
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_3049_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3041_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3041_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3023_);
lean_del_object(v___x_2887_);
lean_dec(v_tail_2885_);
lean_dec(v_head_2884_);
lean_dec(v_cs_x27_2757_);
lean_dec(v_c_x3f_2756_);
v_a_3057_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3033_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3033_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3104_, lean_object* v_c_x3f_3105_, lean_object* v_cs_x27_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3104_, v_c_x3f_3105_, v_cs_x27_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3119_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3166_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3166_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3166_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_unbox(v_a_3131_);
lean_dec(v_a_3131_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_del_object(v___x_3133_);
v___x_3136_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3119_, v_a_3121_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3153_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3153_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3153_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_unbox(v_a_3137_);
lean_dec(v_a_3137_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v_toGoalState_3143_; lean_object* v_split_3144_; lean_object* v_candidates_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_del_object(v___x_3139_);
v___x_3142_ = lean_st_ref_get(v_a_3119_);
v_toGoalState_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_ref(v_toGoalState_3143_);
lean_dec(v___x_3142_);
v_split_3144_ = lean_ctor_get(v_toGoalState_3143_, 15);
lean_inc_ref(v_split_3144_);
lean_dec_ref(v_toGoalState_3143_);
v_candidates_3145_ = lean_ctor_get(v_split_3144_, 1);
lean_inc(v_candidates_3145_);
lean_dec_ref(v_split_3144_);
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_box(0);
v___x_3148_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3145_, v___x_3146_, v___x_3147_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec(v_a_3119_);
v___x_3149_ = lean_box(0);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3149_);
v___x_3151_ = v___x_3139_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec(v_a_3119_);
v_a_3154_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3136_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3136_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec(v_a_3119_);
v___x_3162_ = lean_box(0);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3162_);
v___x_3164_ = v___x_3133_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
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
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec(v_a_3119_);
v_a_3167_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3130_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3130_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
return v_res_3186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_box(0);
v___x_3195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3196_ = l_Lean_mkConst(v___x_3195_, v___x_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3197_){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3199_ = l_Lean_Expr_app___override(v___x_3198_, v_c_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = lean_box(0);
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3210_ = l_Lean_mkConst(v___x_3209_, v___x_3208_);
return v___x_3210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_box(0);
v___x_3217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3218_ = l_Lean_mkConst(v___x_3217_, v___x_3216_);
return v___x_3218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_box(0);
v___x_3225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3226_ = l_Lean_mkConst(v___x_3225_, v___x_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; uint8_t v___y_3250_; lean_object* v___x_3286_; 
lean_inc_ref(v_c_3227_);
v___x_3286_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3227_, v_a_3235_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3372_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3372_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3372_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = l_Lean_Expr_cleanupAnnotations(v_a_3287_);
v___x_3305_ = l_Lean_Expr_isApp(v___x_3304_);
if (v___x_3305_ == 0)
{
lean_dec_ref(v___x_3304_);
lean_del_object(v___x_3289_);
v___y_3292_ = v_a_3228_;
v___y_3293_ = v_a_3229_;
v___y_3294_ = v_a_3230_;
v___y_3295_ = v_a_3231_;
v___y_3296_ = v_a_3232_;
v___y_3297_ = v_a_3233_;
v___y_3298_ = v_a_3234_;
v___y_3299_ = v_a_3235_;
v___y_3300_ = v_a_3236_;
v___y_3301_ = v_a_3237_;
goto v___jp_3291_;
}
else
{
lean_object* v_arg_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v_arg_3306_ = lean_ctor_get(v___x_3304_, 1);
lean_inc_ref(v_arg_3306_);
v___x_3307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3304_);
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3309_ = l_Lean_Expr_isConstOf(v___x_3307_, v___x_3308_);
if (v___x_3309_ == 0)
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Lean_Expr_isApp(v___x_3307_);
if (v___x_3310_ == 0)
{
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_arg_3306_);
lean_del_object(v___x_3289_);
v___y_3292_ = v_a_3228_;
v___y_3293_ = v_a_3229_;
v___y_3294_ = v_a_3230_;
v___y_3295_ = v_a_3231_;
v___y_3296_ = v_a_3232_;
v___y_3297_ = v_a_3233_;
v___y_3298_ = v_a_3234_;
v___y_3299_ = v_a_3235_;
v___y_3300_ = v_a_3236_;
v___y_3301_ = v_a_3237_;
goto v___jp_3291_;
}
else
{
lean_object* v_arg_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_arg_3311_ = lean_ctor_get(v___x_3307_, 1);
lean_inc_ref(v_arg_3311_);
v___x_3312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3307_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_3314_ = l_Lean_Expr_isConstOf(v___x_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
uint8_t v___x_3315_; 
v___x_3315_ = l_Lean_Expr_isApp(v___x_3312_);
if (v___x_3315_ == 0)
{
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
lean_del_object(v___x_3289_);
v___y_3292_ = v_a_3228_;
v___y_3293_ = v_a_3229_;
v___y_3294_ = v_a_3230_;
v___y_3295_ = v_a_3231_;
v___y_3296_ = v_a_3232_;
v___y_3297_ = v_a_3233_;
v___y_3298_ = v_a_3234_;
v___y_3299_ = v_a_3235_;
v___y_3300_ = v_a_3236_;
v___y_3301_ = v_a_3237_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3312_);
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15));
v___x_3318_ = l_Lean_Expr_isConstOf(v___x_3316_, v___x_3317_);
lean_dec_ref(v___x_3316_);
if (v___x_3318_ == 0)
{
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
lean_del_object(v___x_3289_);
v___y_3292_ = v_a_3228_;
v___y_3293_ = v_a_3229_;
v___y_3294_ = v_a_3230_;
v___y_3295_ = v_a_3231_;
v___y_3296_ = v_a_3232_;
v___y_3297_ = v_a_3233_;
v___y_3298_ = v_a_3234_;
v___y_3299_ = v_a_3235_;
v___y_3300_ = v_a_3236_;
v___y_3301_ = v_a_3237_;
goto v___jp_3291_;
}
else
{
uint8_t v___x_3319_; 
lean_inc_ref(v_c_3227_);
v___x_3319_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3227_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
v___x_3320_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3227_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3320_);
v___x_3322_ = v___x_3289_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
lean_object* v___x_3324_; 
lean_del_object(v___x_3289_);
lean_inc_ref(v_c_3227_);
v___x_3324_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3227_, v_a_3228_, v_a_3232_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; uint8_t v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = lean_unbox(v_a_3325_);
lean_dec(v_a_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3337_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3337_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3337_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3333_ = l_Lean_mkApp3(v___x_3332_, v_arg_3311_, v_arg_3306_, v_a_3328_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3333_);
v___x_3335_ = v___x_3330_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
return v___x_3327_;
}
}
else
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3348_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3348_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3348_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3344_ = l_Lean_mkApp3(v___x_3343_, v_arg_3311_, v_arg_3306_, v_a_3339_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3344_);
v___x_3346_ = v___x_3341_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
else
{
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
return v___x_3338_;
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_c_3227_);
v_a_3349_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3324_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3324_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3357_; 
lean_dec_ref(v___x_3312_);
lean_del_object(v___x_3289_);
v___x_3357_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3367_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3367_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3367_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3363_ = l_Lean_mkApp3(v___x_3362_, v_arg_3311_, v_arg_3306_, v_a_3358_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3363_);
v___x_3365_ = v___x_3360_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
else
{
lean_dec_ref(v_arg_3311_);
lean_dec_ref(v_arg_3306_);
return v___x_3357_;
}
}
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
lean_dec_ref(v___x_3307_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_c_3227_);
v___x_3368_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3306_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3368_);
v___x_3370_ = v___x_3289_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
v___jp_3291_:
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_Meta_Grind_isIte(v_c_3227_);
if (v___x_3302_ == 0)
{
uint8_t v___x_3303_; 
v___x_3303_ = l_Lean_Meta_Grind_isDIte(v_c_3227_);
v___y_3240_ = v___y_3298_;
v___y_3241_ = v___y_3299_;
v___y_3242_ = v___y_3300_;
v___y_3243_ = v___y_3294_;
v___y_3244_ = v___y_3293_;
v___y_3245_ = v___y_3297_;
v___y_3246_ = v___y_3295_;
v___y_3247_ = v___y_3301_;
v___y_3248_ = v___y_3296_;
v___y_3249_ = v___y_3292_;
v___y_3250_ = v___x_3303_;
goto v___jp_3239_;
}
else
{
v___y_3240_ = v___y_3298_;
v___y_3241_ = v___y_3299_;
v___y_3242_ = v___y_3300_;
v___y_3243_ = v___y_3294_;
v___y_3244_ = v___y_3293_;
v___y_3245_ = v___y_3297_;
v___y_3246_ = v___y_3295_;
v___y_3247_ = v___y_3301_;
v___y_3248_ = v___y_3296_;
v___y_3249_ = v___y_3292_;
v___y_3250_ = v___x_3302_;
goto v___jp_3239_;
}
}
}
}
else
{
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_c_3227_);
return v___x_3286_;
}
v___jp_3239_:
{
if (v___y_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_inc_ref(v_c_3227_);
v___x_3251_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3227_, v___y_3249_, v___y_3248_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3247_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3270_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3270_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3270_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_unbox(v_a_3252_);
lean_dec(v_a_3252_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3258_; 
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v_c_3227_);
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_c_3227_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
else
{
lean_object* v___x_3260_; 
lean_del_object(v___x_3254_);
lean_inc_ref(v_c_3227_);
v___x_3260_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3227_, v___y_3249_, v___y_3244_, v___y_3243_, v___y_3246_, v___y_3248_, v___y_3245_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3247_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3269_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3269_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3269_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3227_, v_a_3261_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3265_);
v___x_3267_ = v___x_3263_;
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
else
{
lean_dec_ref(v_c_3227_);
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v_c_3227_);
v_a_3271_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3251_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3251_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
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
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
v___x_3279_ = lean_unsigned_to_nat(1u);
v___x_3280_ = l_Lean_Expr_getAppNumArgs(v_c_3227_);
v___x_3281_ = lean_nat_sub(v___x_3280_, v___x_3279_);
lean_dec(v___x_3280_);
v___x_3282_ = lean_nat_sub(v___x_3281_, v___x_3279_);
lean_dec(v___x_3281_);
v___x_3283_ = l_Lean_Expr_getRevArg_x21(v_c_3227_, v___x_3282_);
lean_dec_ref(v_c_3227_);
v___x_3284_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
return v___x_3285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3386_, lean_object* v_major_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3388_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; uint8_t v_trace_3397_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref(v___x_3395_);
v_trace_3397_ = lean_ctor_get_uint8(v_a_3396_, sizeof(void*)*11);
lean_dec(v_a_3396_);
if (v_trace_3397_ == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_Meta_Grind_cases(v_mvarId_3386_, v_major_3387_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
return v___x_3398_;
}
else
{
lean_object* v___x_3399_; 
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
lean_inc(v_a_3391_);
lean_inc_ref(v_a_3390_);
lean_inc_ref(v_major_3387_);
v___x_3399_ = lean_infer_type(v_major_3387_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
lean_inc(v_a_3391_);
lean_inc_ref(v_a_3390_);
v___x_3401_ = l_Lean_Meta_whnfD(v_a_3400_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = l_Lean_Expr_getAppFn(v_a_3402_);
lean_dec(v_a_3402_);
if (lean_obj_tag(v___x_3403_) == 4)
{
lean_object* v_declName_3404_; lean_object* v___x_3405_; 
v_declName_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_declName_3404_);
lean_dec_ref(v___x_3403_);
v___x_3405_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3404_, v_a_3389_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3406_; 
lean_dec_ref(v___x_3405_);
v___x_3406_ = l_Lean_Meta_Grind_cases(v_mvarId_3386_, v_major_3387_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
return v___x_3406_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec_ref(v_major_3387_);
lean_dec(v_mvarId_3386_);
v_a_3407_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3405_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3405_);
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
else
{
lean_object* v___x_3415_; 
lean_dec_ref(v___x_3403_);
v___x_3415_ = l_Lean_Meta_Grind_cases(v_mvarId_3386_, v_major_3387_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
return v___x_3415_;
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec_ref(v_major_3387_);
lean_dec(v_mvarId_3386_);
v_a_3416_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3401_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3401_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec_ref(v_major_3387_);
lean_dec(v_mvarId_3386_);
v_a_3424_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3399_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3399_);
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
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec_ref(v_major_3387_);
lean_dec(v_mvarId_3386_);
v_a_3432_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3395_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3395_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3440_, lean_object* v_major_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3440_, v_major_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3450_, lean_object* v_major_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3450_, v_major_3451_, v_a_3454_, v_a_3455_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3464_, lean_object* v_major_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3464_, v_major_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec_ref(v_a_3468_);
lean_dec(v_a_3467_);
lean_dec(v_a_3466_);
return v_res_3477_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3478_){
_start:
{
uint64_t v_anchor_3479_; 
v_anchor_3479_ = lean_ctor_get_uint64(v_e_3478_, sizeof(void*)*3);
return v_anchor_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3480_){
_start:
{
uint64_t v_res_3481_; lean_object* v_r_3482_; 
v_res_3481_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3480_);
lean_dec_ref(v_e_3480_);
v_r_3482_ = lean_box_uint64(v_res_3481_);
return v_r_3482_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3485_, lean_object* v_x_3486_){
_start:
{
if (lean_obj_tag(v_x_3486_) == 0)
{
uint8_t v___x_3487_; 
v___x_3487_ = 0;
return v___x_3487_;
}
else
{
lean_object* v_key_3488_; lean_object* v_tail_3489_; uint64_t v___x_3490_; uint8_t v___x_3491_; 
v_key_3488_ = lean_ctor_get(v_x_3486_, 0);
v_tail_3489_ = lean_ctor_get(v_x_3486_, 2);
v___x_3490_ = lean_unbox_uint64(v_key_3488_);
v___x_3491_ = lean_uint64_dec_eq(v___x_3490_, v_a_3485_);
if (v___x_3491_ == 0)
{
v_x_3486_ = v_tail_3489_;
goto _start;
}
else
{
return v___x_3491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3493_, lean_object* v_x_3494_){
_start:
{
uint64_t v_a_boxed_3495_; uint8_t v_res_3496_; lean_object* v_r_3497_; 
v_a_boxed_3495_ = lean_unbox_uint64(v_a_3493_);
lean_dec_ref(v_a_3493_);
v_res_3496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3495_, v_x_3494_);
lean_dec(v_x_3494_);
v_r_3497_ = lean_box(v_res_3496_);
return v_r_3497_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3498_, uint64_t v_a_3499_){
_start:
{
lean_object* v_buckets_3500_; lean_object* v___x_3501_; uint64_t v___x_3502_; uint64_t v___x_3503_; uint64_t v_fold_3504_; uint64_t v___x_3505_; uint64_t v___x_3506_; uint64_t v___x_3507_; size_t v___x_3508_; size_t v___x_3509_; size_t v___x_3510_; size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_buckets_3500_ = lean_ctor_get(v_m_3498_, 1);
v___x_3501_ = lean_array_get_size(v_buckets_3500_);
v___x_3502_ = 32ULL;
v___x_3503_ = lean_uint64_shift_right(v_a_3499_, v___x_3502_);
v_fold_3504_ = lean_uint64_xor(v_a_3499_, v___x_3503_);
v___x_3505_ = 16ULL;
v___x_3506_ = lean_uint64_shift_right(v_fold_3504_, v___x_3505_);
v___x_3507_ = lean_uint64_xor(v_fold_3504_, v___x_3506_);
v___x_3508_ = lean_uint64_to_usize(v___x_3507_);
v___x_3509_ = lean_usize_of_nat(v___x_3501_);
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_sub(v___x_3509_, v___x_3510_);
v___x_3512_ = lean_usize_land(v___x_3508_, v___x_3511_);
v___x_3513_ = lean_array_uget_borrowed(v_buckets_3500_, v___x_3512_);
v___x_3514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3499_, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3515_, lean_object* v_a_3516_){
_start:
{
uint64_t v_a_boxed_3517_; uint8_t v_res_3518_; lean_object* v_r_3519_; 
v_a_boxed_3517_ = lean_unbox_uint64(v_a_3516_);
lean_dec_ref(v_a_3516_);
v_res_3518_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3515_, v_a_boxed_3517_);
lean_dec_ref(v_m_3515_);
v_r_3519_ = lean_box(v_res_3518_);
return v_r_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_x_3520_, lean_object* v_x_3521_){
_start:
{
if (lean_obj_tag(v_x_3521_) == 0)
{
return v_x_3520_;
}
else
{
lean_object* v_key_3522_; lean_object* v_value_3523_; lean_object* v_tail_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3548_; 
v_key_3522_ = lean_ctor_get(v_x_3521_, 0);
v_value_3523_ = lean_ctor_get(v_x_3521_, 1);
v_tail_3524_ = lean_ctor_get(v_x_3521_, 2);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_x_3521_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3526_ = v_x_3521_;
v_isShared_3527_ = v_isSharedCheck_3548_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_tail_3524_);
lean_inc(v_value_3523_);
lean_inc(v_key_3522_);
lean_dec(v_x_3521_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3548_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; uint64_t v___x_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; uint64_t v___x_3532_; uint64_t v_fold_3533_; uint64_t v___x_3534_; uint64_t v___x_3535_; uint64_t v___x_3536_; size_t v___x_3537_; size_t v___x_3538_; size_t v___x_3539_; size_t v___x_3540_; size_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3528_ = lean_array_get_size(v_x_3520_);
v___x_3529_ = 32ULL;
v___x_3530_ = lean_unbox_uint64(v_key_3522_);
v___x_3531_ = lean_uint64_shift_right(v___x_3530_, v___x_3529_);
v___x_3532_ = lean_unbox_uint64(v_key_3522_);
v_fold_3533_ = lean_uint64_xor(v___x_3532_, v___x_3531_);
v___x_3534_ = 16ULL;
v___x_3535_ = lean_uint64_shift_right(v_fold_3533_, v___x_3534_);
v___x_3536_ = lean_uint64_xor(v_fold_3533_, v___x_3535_);
v___x_3537_ = lean_uint64_to_usize(v___x_3536_);
v___x_3538_ = lean_usize_of_nat(v___x_3528_);
v___x_3539_ = ((size_t)1ULL);
v___x_3540_ = lean_usize_sub(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_usize_land(v___x_3537_, v___x_3540_);
v___x_3542_ = lean_array_uget_borrowed(v_x_3520_, v___x_3541_);
lean_inc(v___x_3542_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 2, v___x_3542_);
v___x_3544_ = v___x_3526_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_key_3522_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_value_3523_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_array_uset(v_x_3520_, v___x_3541_, v___x_3544_);
v_x_3520_ = v___x_3545_;
v_x_3521_ = v_tail_3524_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_i_3549_, lean_object* v_source_3550_, lean_object* v_target_3551_){
_start:
{
lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = lean_array_get_size(v_source_3550_);
v___x_3553_ = lean_nat_dec_lt(v_i_3549_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_dec_ref(v_source_3550_);
lean_dec(v_i_3549_);
return v_target_3551_;
}
else
{
lean_object* v_es_3554_; lean_object* v___x_3555_; lean_object* v_source_3556_; lean_object* v_target_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_es_3554_ = lean_array_fget(v_source_3550_, v_i_3549_);
v___x_3555_ = lean_box(0);
v_source_3556_ = lean_array_fset(v_source_3550_, v_i_3549_, v___x_3555_);
v_target_3557_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(v_target_3551_, v_es_3554_);
v___x_3558_ = lean_unsigned_to_nat(1u);
v___x_3559_ = lean_nat_add(v_i_3549_, v___x_3558_);
lean_dec(v_i_3549_);
v_i_3549_ = v___x_3559_;
v_source_3550_ = v_source_3556_;
v_target_3551_ = v_target_3557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_data_3561_){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v_nbuckets_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3562_ = lean_array_get_size(v_data_3561_);
v___x_3563_ = lean_unsigned_to_nat(2u);
v_nbuckets_3564_ = lean_nat_mul(v___x_3562_, v___x_3563_);
v___x_3565_ = lean_unsigned_to_nat(0u);
v___x_3566_ = lean_box(0);
v___x_3567_ = lean_mk_array(v_nbuckets_3564_, v___x_3566_);
v___x_3568_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v___x_3565_, v_data_3561_, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3569_, uint64_t v_a_3570_, lean_object* v_b_3571_){
_start:
{
lean_object* v_size_3572_; lean_object* v_buckets_3573_; lean_object* v___x_3574_; uint64_t v___x_3575_; uint64_t v___x_3576_; uint64_t v_fold_3577_; uint64_t v___x_3578_; uint64_t v___x_3579_; uint64_t v___x_3580_; size_t v___x_3581_; size_t v___x_3582_; size_t v___x_3583_; size_t v___x_3584_; size_t v___x_3585_; lean_object* v_bkt_3586_; uint8_t v___x_3587_; 
v_size_3572_ = lean_ctor_get(v_m_3569_, 0);
v_buckets_3573_ = lean_ctor_get(v_m_3569_, 1);
v___x_3574_ = lean_array_get_size(v_buckets_3573_);
v___x_3575_ = 32ULL;
v___x_3576_ = lean_uint64_shift_right(v_a_3570_, v___x_3575_);
v_fold_3577_ = lean_uint64_xor(v_a_3570_, v___x_3576_);
v___x_3578_ = 16ULL;
v___x_3579_ = lean_uint64_shift_right(v_fold_3577_, v___x_3578_);
v___x_3580_ = lean_uint64_xor(v_fold_3577_, v___x_3579_);
v___x_3581_ = lean_uint64_to_usize(v___x_3580_);
v___x_3582_ = lean_usize_of_nat(v___x_3574_);
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_sub(v___x_3582_, v___x_3583_);
v___x_3585_ = lean_usize_land(v___x_3581_, v___x_3584_);
v_bkt_3586_ = lean_array_uget_borrowed(v_buckets_3573_, v___x_3585_);
v___x_3587_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3570_, v_bkt_3586_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3609_; 
lean_inc_ref(v_buckets_3573_);
lean_inc(v_size_3572_);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_m_3569_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; lean_object* v_unused_3611_; 
v_unused_3610_ = lean_ctor_get(v_m_3569_, 1);
lean_dec(v_unused_3610_);
v_unused_3611_ = lean_ctor_get(v_m_3569_, 0);
lean_dec(v_unused_3611_);
v___x_3589_ = v_m_3569_;
v_isShared_3590_ = v_isSharedCheck_3609_;
goto v_resetjp_3588_;
}
else
{
lean_dec(v_m_3569_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3609_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v_size_x27_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v_buckets_x27_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3591_ = lean_unsigned_to_nat(1u);
v_size_x27_3592_ = lean_nat_add(v_size_3572_, v___x_3591_);
lean_dec(v_size_3572_);
v___x_3593_ = lean_box_uint64(v_a_3570_);
lean_inc(v_bkt_3586_);
v___x_3594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v_b_3571_);
lean_ctor_set(v___x_3594_, 2, v_bkt_3586_);
v_buckets_x27_3595_ = lean_array_uset(v_buckets_3573_, v___x_3585_, v___x_3594_);
v___x_3596_ = lean_unsigned_to_nat(4u);
v___x_3597_ = lean_nat_mul(v_size_x27_3592_, v___x_3596_);
v___x_3598_ = lean_unsigned_to_nat(3u);
v___x_3599_ = lean_nat_div(v___x_3597_, v___x_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_array_get_size(v_buckets_x27_3595_);
v___x_3601_ = lean_nat_dec_le(v___x_3599_, v___x_3600_);
lean_dec(v___x_3599_);
if (v___x_3601_ == 0)
{
lean_object* v_val_3602_; lean_object* v___x_3604_; 
v_val_3602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_buckets_x27_3595_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v_val_3602_);
lean_ctor_set(v___x_3589_, 0, v_size_x27_3592_);
v___x_3604_ = v___x_3589_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_size_x27_3592_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_val_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
else
{
lean_object* v___x_3607_; 
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v_buckets_x27_3595_);
lean_ctor_set(v___x_3589_, 0, v_size_x27_3592_);
v___x_3607_ = v___x_3589_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_size_x27_3592_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_buckets_x27_3595_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_dec(v_b_3571_);
return v_m_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3612_, lean_object* v_a_3613_, lean_object* v_b_3614_){
_start:
{
uint64_t v_a_boxed_3615_; lean_object* v_res_3616_; 
v_a_boxed_3615_ = lean_unbox_uint64(v_a_3613_);
lean_dec_ref(v_a_3613_);
v_res_3616_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3612_, v_a_boxed_3615_, v_b_3614_);
return v_res_3616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_box(0);
v___x_3618_ = lean_unsigned_to_nat(16u);
v___x_3619_ = lean_mk_array(v___x_3618_, v___x_3617_);
return v___x_3619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v_found_3622_; 
v___x_3620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3621_ = lean_unsigned_to_nat(0u);
v_found_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3622_, 0, v___x_3621_);
lean_ctor_set(v_found_3622_, 1, v___x_3620_);
return v_found_3622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_found_3623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3624_ = lean_box(0);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v_found_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3626_, lean_object* v_numDigits_3627_, lean_object* v_es_3628_, lean_object* v_as_3629_, size_t v_sz_3630_, size_t v_i_3631_, lean_object* v_b_3632_){
_start:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_usize_dec_lt(v_i_3631_, v_sz_3630_);
if (v___x_3633_ == 0)
{
return v_b_3632_;
}
else
{
lean_object* v_snd_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3659_; 
v_snd_3634_ = lean_ctor_get(v_b_3632_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_b_3632_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_b_3632_, 0);
lean_dec(v_unused_3660_);
v___x_3636_ = v_b_3632_;
v_isShared_3637_ = v_isSharedCheck_3659_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_snd_3634_);
lean_dec(v_b_3632_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3659_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v_a_3638_; uint64_t v_anchor_3639_; uint64_t v___x_3640_; uint64_t v___x_3641_; uint8_t v___x_3642_; 
v_a_3638_ = lean_array_uget_borrowed(v_as_3629_, v_i_3631_);
v_anchor_3639_ = lean_ctor_get_uint64(v_a_3638_, sizeof(void*)*3);
v___x_3640_ = lean_uint64_of_nat(v_shift_3626_);
v___x_3641_ = lean_uint64_shift_right(v_anchor_3639_, v___x_3640_);
v___x_3642_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3634_, v___x_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_box(0);
v___x_3645_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3634_, v___x_3641_, v___x_3644_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 1, v___x_3645_);
lean_ctor_set(v___x_3636_, 0, v___x_3643_);
v___x_3647_ = v___x_3636_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
size_t v___x_3648_; size_t v___x_3649_; 
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3631_, v___x_3648_);
v_i_3631_ = v___x_3649_;
v_b_3632_ = v___x_3647_;
goto _start;
}
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3652_ = lean_unsigned_to_nat(1u);
v___x_3653_ = lean_nat_add(v_numDigits_3627_, v___x_3652_);
v___x_3654_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3628_, v___x_3653_);
lean_dec(v___x_3653_);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3655_);
v___x_3657_ = v___x_3636_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_snd_3634_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3661_, lean_object* v_numDigits_3662_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v___x_3663_ = lean_unsigned_to_nat(4u);
v___x_3664_ = lean_nat_mul(v___x_3663_, v_numDigits_3662_);
v___x_3665_ = lean_unsigned_to_nat(64u);
v___x_3666_ = lean_nat_dec_lt(v___x_3664_, v___x_3665_);
if (v___x_3666_ == 0)
{
lean_dec(v___x_3664_);
lean_inc(v_numDigits_3662_);
return v_numDigits_3662_;
}
else
{
lean_object* v_shift_3667_; lean_object* v___x_3668_; size_t v_sz_3669_; size_t v___x_3670_; lean_object* v___x_3671_; lean_object* v_fst_3672_; 
v_shift_3667_ = lean_nat_sub(v___x_3665_, v___x_3664_);
lean_dec(v___x_3664_);
v___x_3668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3669_ = lean_array_size(v_es_3661_);
v___x_3670_ = ((size_t)0ULL);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3667_, v_numDigits_3662_, v_es_3661_, v_es_3661_, v_sz_3669_, v___x_3670_, v___x_3668_);
lean_dec(v_shift_3667_);
v_fst_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_fst_3672_);
lean_dec_ref(v___x_3671_);
if (lean_obj_tag(v_fst_3672_) == 0)
{
lean_inc(v_numDigits_3662_);
return v_numDigits_3662_;
}
else
{
lean_object* v_val_3673_; 
v_val_3673_ = lean_ctor_get(v_fst_3672_, 0);
lean_inc(v_val_3673_);
lean_dec_ref(v_fst_3672_);
return v_val_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3674_, lean_object* v_numDigits_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3674_, v_numDigits_3675_);
lean_dec(v_numDigits_3675_);
lean_dec_ref(v_es_3674_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3677_, lean_object* v_numDigits_3678_, lean_object* v_es_3679_, lean_object* v_as_3680_, lean_object* v_sz_3681_, lean_object* v_i_3682_, lean_object* v_b_3683_){
_start:
{
size_t v_sz_boxed_3684_; size_t v_i_boxed_3685_; lean_object* v_res_3686_; 
v_sz_boxed_3684_ = lean_unbox_usize(v_sz_3681_);
lean_dec(v_sz_3681_);
v_i_boxed_3685_ = lean_unbox_usize(v_i_3682_);
lean_dec(v_i_3682_);
v_res_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3677_, v_numDigits_3678_, v_es_3679_, v_as_3680_, v_sz_boxed_3684_, v_i_boxed_3685_, v_b_3683_);
lean_dec_ref(v_as_3680_);
lean_dec_ref(v_es_3679_);
lean_dec(v_numDigits_3678_);
lean_dec(v_shift_3677_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_unsigned_to_nat(4u);
v___x_3689_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3687_, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3690_);
lean_dec_ref(v_es_3690_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3692_, lean_object* v_as_3693_, size_t v_i_3694_, size_t v_stop_3695_, lean_object* v_b_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_a_3709_; uint8_t v___x_3713_; 
v___x_3713_ = lean_usize_dec_eq(v_i_3694_, v_stop_3695_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_array_uget_borrowed(v_as_3693_, v_i_3694_);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
v___x_3715_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3714_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref(v___x_3715_);
v___x_3717_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3714_);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
lean_inc(v___y_3698_);
lean_inc(v___y_3697_);
lean_inc(v___x_3714_);
v___x_3718_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3714_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref(v___x_3718_);
if (lean_obj_tag(v_a_3719_) == 2)
{
lean_object* v_numCases_3720_; uint8_t v_isRec_3721_; lean_object* v___x_3722_; 
v_numCases_3720_ = lean_ctor_get(v_a_3719_, 0);
lean_inc(v_numCases_3720_);
v_isRec_3721_ = lean_ctor_get_uint8(v_a_3719_, sizeof(void*)*1);
lean_dec_ref(v_a_3719_);
lean_inc_ref(v_filter_3692_);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
lean_inc(v___y_3698_);
lean_inc(v___y_3697_);
lean_inc_ref(v___x_3717_);
v___x_3722_ = lean_apply_12(v_filter_3692_, v___x_3717_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, lean_box(0));
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; uint8_t v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = lean_unbox(v_a_3723_);
lean_dec(v_a_3723_);
if (v___x_3724_ == 0)
{
lean_dec(v_numCases_3720_);
lean_dec_ref(v___x_3717_);
lean_dec(v_a_3716_);
v_a_3709_ = v_b_3696_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3725_; uint64_t v___x_3726_; lean_object* v___x_3727_; 
lean_inc(v___x_3714_);
v___x_3725_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3725_, 0, v___x_3714_);
lean_ctor_set(v___x_3725_, 1, v_numCases_3720_);
lean_ctor_set(v___x_3725_, 2, v___x_3717_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*3 + 8, v_isRec_3721_);
v___x_3726_ = lean_unbox_uint64(v_a_3716_);
lean_dec(v_a_3716_);
lean_ctor_set_uint64(v___x_3725_, sizeof(void*)*3, v___x_3726_);
v___x_3727_ = lean_array_push(v_b_3696_, v___x_3725_);
v_a_3709_ = v___x_3727_;
goto v___jp_3708_;
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_numCases_3720_);
lean_dec_ref(v___x_3717_);
lean_dec(v_a_3716_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v_b_3696_);
lean_dec_ref(v_filter_3692_);
v_a_3728_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3722_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3722_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_dec(v_a_3719_);
lean_dec_ref(v___x_3717_);
lean_dec(v_a_3716_);
v_a_3709_ = v_b_3696_;
goto v___jp_3708_;
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref(v___x_3717_);
lean_dec(v_a_3716_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v_b_3696_);
lean_dec_ref(v_filter_3692_);
v_a_3736_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3718_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3718_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v_b_3696_);
lean_dec_ref(v_filter_3692_);
v_a_3744_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3715_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3715_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v___x_3752_; 
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v_filter_3692_);
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_b_3696_);
return v___x_3752_;
}
v___jp_3708_:
{
size_t v___x_3710_; size_t v___x_3711_; 
v___x_3710_ = ((size_t)1ULL);
v___x_3711_ = lean_usize_add(v_i_3694_, v___x_3710_);
v_i_3694_ = v___x_3711_;
v_b_3696_ = v_a_3709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3753_, lean_object* v_as_3754_, lean_object* v_i_3755_, lean_object* v_stop_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
size_t v_i_boxed_3769_; size_t v_stop_boxed_3770_; lean_object* v_res_3771_; 
v_i_boxed_3769_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_stop_boxed_3770_ = lean_unbox_usize(v_stop_3756_);
lean_dec(v_stop_3756_);
v_res_3771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3753_, v_as_3754_, v_i_boxed_3769_, v_stop_boxed_3770_, v_b_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec_ref(v_as_3754_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3774_, lean_object* v_as_3775_, lean_object* v_start_3776_, lean_object* v_stop_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3789_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3790_ = lean_nat_dec_lt(v_start_3776_, v_stop_3777_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v_filter_3774_);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = lean_array_get_size(v_as_3775_);
v___x_3793_ = lean_nat_dec_le(v_stop_3777_, v___x_3792_);
if (v___x_3793_ == 0)
{
uint8_t v___x_3794_; 
v___x_3794_ = lean_nat_dec_lt(v_start_3776_, v___x_3792_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; 
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v_filter_3774_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3789_);
return v___x_3795_;
}
else
{
size_t v___x_3796_; size_t v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = lean_usize_of_nat(v_start_3776_);
v___x_3797_ = lean_usize_of_nat(v___x_3792_);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3774_, v_as_3775_, v___x_3796_, v___x_3797_, v___x_3789_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
return v___x_3798_;
}
}
else
{
size_t v___x_3799_; size_t v___x_3800_; lean_object* v___x_3801_; 
v___x_3799_ = lean_usize_of_nat(v_start_3776_);
v___x_3800_ = lean_usize_of_nat(v_stop_3777_);
v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3774_, v_as_3775_, v___x_3799_, v___x_3800_, v___x_3789_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3802_, lean_object* v_as_3803_, lean_object* v_start_3804_, lean_object* v_stop_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3802_, v_as_3803_, v_start_3804_, v_stop_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v_stop_3805_);
lean_dec(v_start_3804_);
lean_dec_ref(v_as_3803_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___x_3830_; lean_object* v_toGoalState_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3861_; 
v___x_3830_ = lean_st_ref_get(v_a_3819_);
v_toGoalState_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; 
v_unused_3862_ = lean_ctor_get(v___x_3830_, 1);
lean_dec(v_unused_3862_);
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3861_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_toGoalState_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3861_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v_split_3835_; lean_object* v_candidates_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_split_3835_ = lean_ctor_get(v_toGoalState_3831_, 15);
lean_inc_ref(v_split_3835_);
lean_dec_ref(v_toGoalState_3831_);
v_candidates_3836_ = lean_ctor_get(v_split_3835_, 1);
lean_inc(v_candidates_3836_);
lean_dec_ref(v_split_3835_);
v___x_3837_ = lean_array_mk(v_candidates_3836_);
v___x_3838_ = lean_unsigned_to_nat(0u);
v___x_3839_ = lean_array_get_size(v___x_3837_);
v___x_3840_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3818_, v___x_3837_, v___x_3838_, v___x_3839_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec_ref(v___x_3837_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3852_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3852_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3852_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3845_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3841_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 1, v___x_3845_);
lean_ctor_set(v___x_3833_, 0, v_a_3841_);
v___x_3847_ = v___x_3833_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3841_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3849_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3847_);
v___x_3849_ = v___x_3843_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_del_object(v___x_3833_);
v_a_3853_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3840_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3840_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3876_, lean_object* v_m_3877_, uint64_t v_a_3878_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3877_, v_a_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3880_, lean_object* v_m_3881_, lean_object* v_a_3882_){
_start:
{
uint64_t v_a_boxed_3883_; uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_a_boxed_3883_ = lean_unbox_uint64(v_a_3882_);
lean_dec_ref(v_a_3882_);
v_res_3884_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_3880_, v_m_3881_, v_a_boxed_3883_);
lean_dec_ref(v_m_3881_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3886_, lean_object* v_m_3887_, uint64_t v_a_3888_, lean_object* v_b_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3887_, v_a_3888_, v_b_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3891_, lean_object* v_m_3892_, lean_object* v_a_3893_, lean_object* v_b_3894_){
_start:
{
uint64_t v_a_boxed_3895_; lean_object* v_res_3896_; 
v_a_boxed_3895_ = lean_unbox_uint64(v_a_3893_);
lean_dec_ref(v_a_3893_);
v_res_3896_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_3891_, v_m_3892_, v_a_boxed_3895_, v_b_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3897_, uint64_t v_a_3898_, lean_object* v_x_3899_){
_start:
{
uint8_t v___x_3900_; 
v___x_3900_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3898_, v_x_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3901_, lean_object* v_a_3902_, lean_object* v_x_3903_){
_start:
{
uint64_t v_a_boxed_3904_; uint8_t v_res_3905_; lean_object* v_r_3906_; 
v_a_boxed_3904_ = lean_unbox_uint64(v_a_3902_);
lean_dec_ref(v_a_3902_);
v_res_3905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_3901_, v_a_boxed_3904_, v_x_3903_);
lean_dec(v_x_3903_);
v_r_3906_ = lean_box(v_res_3905_);
return v_r_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3907_, lean_object* v_data_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_data_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3910_, lean_object* v_i_3911_, lean_object* v_source_3912_, lean_object* v_target_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_i_3911_, v_source_3912_, v_target_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(v_x_3916_, v_x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v_p_3938_; lean_object* v___x_3941_; 
lean_inc_ref(v_proof_3931_);
v___x_3941_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_3931_, v_a_3933_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3980_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3980_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3980_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3962_ = l_Lean_Expr_cleanupAnnotations(v_a_3942_);
v___x_3963_ = l_Lean_Expr_isApp(v___x_3962_);
if (v___x_3963_ == 0)
{
lean_dec_ref(v___x_3962_);
v___y_3947_ = v_a_3932_;
v___y_3948_ = v_a_3933_;
v___y_3949_ = v_a_3934_;
v___y_3950_ = v_a_3935_;
goto v___jp_3946_;
}
else
{
lean_object* v_arg_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v_arg_3964_ = lean_ctor_get(v___x_3962_, 1);
lean_inc_ref(v_arg_3964_);
v___x_3965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3962_);
v___x_3966_ = l_Lean_Expr_isApp(v___x_3965_);
if (v___x_3966_ == 0)
{
lean_dec_ref(v___x_3965_);
lean_dec_ref(v_arg_3964_);
v___y_3947_ = v_a_3932_;
v___y_3948_ = v_a_3933_;
v___y_3949_ = v_a_3934_;
v___y_3950_ = v_a_3935_;
goto v___jp_3946_;
}
else
{
lean_object* v_arg_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v_arg_3967_ = lean_ctor_get(v___x_3965_, 1);
lean_inc_ref(v_arg_3967_);
v___x_3968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3965_);
v___x_3969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_3970_ = l_Lean_Expr_isConstOf(v___x_3968_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
lean_dec_ref(v_arg_3967_);
v___x_3971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_3972_ = l_Lean_Expr_isConstOf(v___x_3968_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_3974_ = l_Lean_Expr_isConstOf(v___x_3968_, v___x_3973_);
lean_dec_ref(v___x_3968_);
if (v___x_3974_ == 0)
{
lean_dec_ref(v_arg_3964_);
v___y_3947_ = v_a_3932_;
v___y_3948_ = v_a_3933_;
v___y_3949_ = v_a_3934_;
v___y_3950_ = v_a_3935_;
goto v___jp_3946_;
}
else
{
lean_del_object(v___x_3944_);
lean_dec_ref(v_proof_3931_);
v_p_3938_ = v_arg_3964_;
goto v___jp_3937_;
}
}
else
{
lean_dec_ref(v___x_3968_);
lean_del_object(v___x_3944_);
lean_dec_ref(v_proof_3931_);
v_p_3938_ = v_arg_3964_;
goto v___jp_3937_;
}
}
else
{
uint8_t v___x_3975_; 
lean_dec_ref(v___x_3968_);
lean_del_object(v___x_3944_);
lean_dec_ref(v_proof_3931_);
v___x_3975_ = l_Lean_Expr_isFalse(v_arg_3967_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec_ref(v_arg_3964_);
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v_arg_3964_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
}
}
v___jp_3946_:
{
if (lean_obj_tag(v_proof_3931_) == 6)
{
lean_object* v_body_3951_; uint8_t v___x_3952_; 
v_body_3951_ = lean_ctor_get(v_proof_3931_, 2);
lean_inc_ref(v_body_3951_);
lean_dec_ref(v_proof_3931_);
v___x_3952_ = l_Lean_Expr_hasLooseBVars(v_body_3951_);
if (v___x_3952_ == 0)
{
lean_del_object(v___x_3944_);
v_proof_3931_ = v_body_3951_;
v_a_3932_ = v___y_3947_;
v_a_3933_ = v___y_3948_;
v_a_3934_ = v___y_3949_;
v_a_3935_ = v___y_3950_;
goto _start;
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
lean_dec_ref(v_body_3951_);
v___x_3954_ = lean_box(0);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v___x_3954_);
v___x_3956_ = v___x_3944_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
lean_dec_ref(v_proof_3931_);
v___x_3958_ = lean_box(0);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v___x_3958_);
v___x_3960_ = v___x_3944_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v_proof_3931_);
v_a_3981_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3941_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3941_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
v___jp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_p_3938_);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_3996_, lean_object* v___y_3997_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = l_Lean_Expr_hasMVar(v_e_3996_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_e_3996_);
return v___x_4000_;
}
else
{
lean_object* v___x_4001_; lean_object* v_mctx_4002_; lean_object* v___x_4003_; lean_object* v_fst_4004_; lean_object* v_snd_4005_; lean_object* v___x_4006_; lean_object* v_cache_4007_; lean_object* v_zetaDeltaFVarIds_4008_; lean_object* v_postponed_4009_; lean_object* v_diag_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4019_; 
v___x_4001_ = lean_st_ref_get(v___y_3997_);
v_mctx_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc_ref(v_mctx_4002_);
lean_dec(v___x_4001_);
v___x_4003_ = l_Lean_instantiateMVarsCore(v_mctx_4002_, v_e_3996_);
v_fst_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_fst_4004_);
v_snd_4005_ = lean_ctor_get(v___x_4003_, 1);
lean_inc(v_snd_4005_);
lean_dec_ref(v___x_4003_);
v___x_4006_ = lean_st_ref_take(v___y_3997_);
v_cache_4007_ = lean_ctor_get(v___x_4006_, 1);
v_zetaDeltaFVarIds_4008_ = lean_ctor_get(v___x_4006_, 2);
v_postponed_4009_ = lean_ctor_get(v___x_4006_, 3);
v_diag_4010_ = lean_ctor_get(v___x_4006_, 4);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4019_ == 0)
{
lean_object* v_unused_4020_; 
v_unused_4020_ = lean_ctor_get(v___x_4006_, 0);
lean_dec(v_unused_4020_);
v___x_4012_ = v___x_4006_;
v_isShared_4013_ = v_isSharedCheck_4019_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_diag_4010_);
lean_inc(v_postponed_4009_);
lean_inc(v_zetaDeltaFVarIds_4008_);
lean_inc(v_cache_4007_);
lean_dec(v___x_4006_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4019_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v_snd_4005_);
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_snd_4005_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v_cache_4007_);
lean_ctor_set(v_reuseFailAlloc_4018_, 2, v_zetaDeltaFVarIds_4008_);
lean_ctor_set(v_reuseFailAlloc_4018_, 3, v_postponed_4009_);
lean_ctor_set(v_reuseFailAlloc_4018_, 4, v_diag_4010_);
v___x_4015_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_st_ref_set(v___y_3997_, v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v_fst_4004_);
return v___x_4017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4021_, v___y_4022_);
lean_dec(v___y_4022_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4025_, v___y_4027_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4039_, lean_object* v_x_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4039_, v_x_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v_a_4055_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4046_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4046_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4063_, lean_object* v_x_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4063_, v_x_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4071_, lean_object* v_mvarId_4072_, lean_object* v_x_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4072_, v_x_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4080_, lean_object* v_mvarId_4081_, lean_object* v_x_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4080_, v_mvarId_4081_, v_x_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___x_4095_; lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4106_; 
v___x_4095_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4089_, v___y_4091_);
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4106_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4106_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
uint8_t v___x_4100_; 
v___x_4100_ = l_Lean_Expr_hasSyntheticSorry(v_a_4096_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; 
lean_del_object(v___x_4098_);
v___x_4101_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4096_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4104_; 
lean_dec(v_a_4096_);
v___x_4102_ = lean_box(0);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4102_);
v___x_4104_ = v___x_4098_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v___f_4121_; lean_object* v___x_4122_; 
lean_inc(v_mvarId_4114_);
v___x_4120_ = l_Lean_mkMVar(v_mvarId_4114_);
v___f_4121_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4121_, 0, v___x_4120_);
v___x_4122_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4114_, v___f_4121_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0(lean_object* v_tac_4153_){
_start:
{
lean_object* v___x_4154_; uint8_t v___x_4155_; uint8_t v___x_4156_; 
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__3));
lean_inc(v_tac_4153_);
v___x_4155_ = l_Lean_Syntax_isOfKind(v_tac_4153_, v___x_4154_);
v___x_4156_ = 1;
if (v___x_4155_ == 0)
{
lean_object* v___x_4157_; uint8_t v___x_4158_; 
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__5));
lean_inc(v_tac_4153_);
v___x_4158_ = l_Lean_Syntax_isOfKind(v_tac_4153_, v___x_4157_);
if (v___x_4158_ == 0)
{
lean_dec(v_tac_4153_);
return v___x_4156_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; 
v___x_4159_ = lean_unsigned_to_nat(1u);
v___x_4160_ = l_Lean_Syntax_getArg(v_tac_4153_, v___x_4159_);
lean_dec(v_tac_4153_);
v___x_4161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7));
v___x_4162_ = l_Lean_Syntax_isOfKind(v___x_4160_, v___x_4161_);
if (v___x_4162_ == 0)
{
return v___x_4156_;
}
else
{
return v___x_4155_;
}
}
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4163_ = lean_unsigned_to_nat(3u);
v___x_4164_ = l_Lean_Syntax_getArg(v_tac_4153_, v___x_4163_);
lean_dec(v_tac_4153_);
v___x_4165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___closed__7));
v___x_4166_ = l_Lean_Syntax_isOfKind(v___x_4164_, v___x_4165_);
if (v___x_4166_ == 0)
{
return v___x_4156_;
}
else
{
uint8_t v___x_4167_; 
v___x_4167_ = 0;
return v___x_4167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0___boxed(lean_object* v_tac_4168_){
_start:
{
uint8_t v_res_4169_; lean_object* v_r_4170_; 
v_res_4169_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___lam__0(v_tac_4168_);
v_r_4170_ = lean_box(v_res_4169_);
return v_r_4170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4172_){
_start:
{
lean_object* v___f_4173_; uint8_t v___x_4174_; 
v___f_4173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___closed__0));
v___x_4174_ = l_List_all___redArg(v_seq_4172_, v___f_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4175_){
_start:
{
uint8_t v_res_4176_; lean_object* v_r_4177_; 
v_res_4176_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4175_);
v_r_4177_ = lean_box(v_res_4176_);
return v_r_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4193_, lean_object* v_a_4194_){
_start:
{
if (lean_obj_tag(v_seq_4193_) == 0)
{
lean_object* v_ref_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_ref_4196_ = lean_ctor_get(v_a_4194_, 5);
v___x_4197_ = 0;
v___x_4198_ = l_Lean_SourceInfo_fromRef(v_ref_4196_, v___x_4197_);
v___x_4199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4198_);
v___x_4201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4198_);
lean_ctor_set(v___x_4201_, 1, v___x_4199_);
v___x_4202_ = l_Lean_Syntax_node1(v___x_4198_, v___x_4200_, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
return v___x_4203_;
}
else
{
lean_object* v_tail_4204_; 
v_tail_4204_ = lean_ctor_get(v_seq_4193_, 1);
if (lean_obj_tag(v_tail_4204_) == 0)
{
lean_object* v_head_4205_; lean_object* v___x_4206_; 
v_head_4205_ = lean_ctor_get(v_seq_4193_, 0);
lean_inc(v_head_4205_);
lean_dec_ref(v_seq_4193_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_head_4205_);
return v___x_4206_;
}
else
{
lean_object* v_head_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4229_; 
lean_inc(v_tail_4204_);
v_head_4207_ = lean_ctor_get(v_seq_4193_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v_seq_4193_);
if (v_isSharedCheck_4229_ == 0)
{
lean_object* v_unused_4230_; 
v_unused_4230_ = lean_ctor_get(v_seq_4193_, 1);
lean_dec(v_unused_4230_);
v___x_4209_ = v_seq_4193_;
v_isShared_4210_ = v_isSharedCheck_4229_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_head_4207_);
lean_dec(v_seq_4193_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4229_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4228_; 
v___x_4211_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4204_, v_a_4194_);
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4214_ = v___x_4211_;
v_isShared_4215_ = v_isSharedCheck_4228_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4211_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4228_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v_ref_4216_; uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4222_; 
v_ref_4216_ = lean_ctor_get(v_a_4194_, 5);
v___x_4217_ = 0;
v___x_4218_ = l_Lean_SourceInfo_fromRef(v_ref_4216_, v___x_4217_);
v___x_4219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4218_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 2);
lean_ctor_set(v___x_4209_, 1, v___x_4220_);
lean_ctor_set(v___x_4209_, 0, v___x_4218_);
v___x_4222_ = v___x_4209_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4218_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4223_ = l_Lean_Syntax_node3(v___x_4218_, v___x_4219_, v_head_4207_, v___x_4222_, v_a_4212_);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4223_);
v___x_4225_ = v___x_4214_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4231_, v_a_4232_);
lean_dec_ref(v_a_4232_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4235_, v_a_4236_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4240_, v_a_4241_, v_a_4242_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4245_, lean_object* v_seq_4246_, lean_object* v_a_4247_){
_start:
{
if (lean_obj_tag(v_seq_4246_) == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_cases_4245_);
return v___x_4249_;
}
else
{
lean_object* v___x_4250_; lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4265_; 
v___x_4250_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4246_, v_a_4247_);
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4253_ = v___x_4250_;
v_isShared_4254_ = v_isSharedCheck_4265_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4250_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4265_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v_ref_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4263_; 
v_ref_4255_ = lean_ctor_get(v_a_4247_, 5);
v___x_4256_ = 0;
v___x_4257_ = l_Lean_SourceInfo_fromRef(v_ref_4255_, v___x_4256_);
v___x_4258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4257_);
v___x_4260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4257_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_Syntax_node3(v___x_4257_, v___x_4258_, v_cases_4245_, v___x_4260_, v_a_4251_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4261_);
v___x_4263_ = v___x_4253_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4266_, lean_object* v_seq_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4266_, v_seq_4267_, v_a_4268_);
lean_dec_ref(v_a_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4271_, lean_object* v_seq_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4271_, v_seq_4272_, v_a_4273_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4277_, lean_object* v_seq_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4277_, v_seq_4278_, v_a_4279_, v_a_4280_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
return v_res_4282_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4283_, lean_object* v_x_4284_){
_start:
{
if (lean_obj_tag(v_x_4283_) == 0)
{
if (lean_obj_tag(v_x_4284_) == 0)
{
uint8_t v___x_4285_; 
v___x_4285_ = 1;
return v___x_4285_;
}
else
{
uint8_t v___x_4286_; 
lean_dec_ref(v_x_4284_);
v___x_4286_ = 0;
return v___x_4286_;
}
}
else
{
if (lean_obj_tag(v_x_4284_) == 0)
{
uint8_t v___x_4287_; 
lean_dec_ref(v_x_4283_);
v___x_4287_ = 0;
return v___x_4287_;
}
else
{
lean_object* v_head_4288_; lean_object* v_tail_4289_; lean_object* v_head_4290_; lean_object* v_tail_4291_; uint8_t v___x_4292_; 
v_head_4288_ = lean_ctor_get(v_x_4283_, 0);
lean_inc(v_head_4288_);
v_tail_4289_ = lean_ctor_get(v_x_4283_, 1);
lean_inc(v_tail_4289_);
lean_dec_ref(v_x_4283_);
v_head_4290_ = lean_ctor_get(v_x_4284_, 0);
lean_inc(v_head_4290_);
v_tail_4291_ = lean_ctor_get(v_x_4284_, 1);
lean_inc(v_tail_4291_);
lean_dec_ref(v_x_4284_);
v___x_4292_ = l_Lean_Syntax_structEq(v_head_4288_, v_head_4290_);
if (v___x_4292_ == 0)
{
lean_dec(v_tail_4291_);
lean_dec(v_tail_4289_);
return v___x_4292_;
}
else
{
v_x_4283_ = v_tail_4289_;
v_x_4284_ = v_tail_4291_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
uint8_t v_res_4296_; lean_object* v_r_4297_; 
v_res_4296_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4294_, v_x_4295_);
v_r_4297_ = lean_box(v_res_4296_);
return v_r_4297_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4298_, uint8_t v___x_4299_, lean_object* v_as_4300_, size_t v_i_4301_, size_t v_stop_4302_){
_start:
{
uint8_t v___x_4303_; 
v___x_4303_ = lean_usize_dec_eq(v_i_4301_, v_stop_4302_);
if (v___x_4303_ == 0)
{
uint8_t v___x_4304_; uint8_t v___y_4306_; lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4304_ = 1;
v___x_4310_ = lean_array_uget_borrowed(v_as_4300_, v_i_4301_);
lean_inc(v_alt_4298_);
lean_inc(v___x_4310_);
v___x_4311_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4310_, v_alt_4298_);
if (v___x_4311_ == 0)
{
v___y_4306_ = v___x_4299_;
goto v___jp_4305_;
}
else
{
v___y_4306_ = v___x_4303_;
goto v___jp_4305_;
}
v___jp_4305_:
{
if (v___y_4306_ == 0)
{
size_t v___x_4307_; size_t v___x_4308_; 
v___x_4307_ = ((size_t)1ULL);
v___x_4308_ = lean_usize_add(v_i_4301_, v___x_4307_);
v_i_4301_ = v___x_4308_;
goto _start;
}
else
{
lean_dec(v_alt_4298_);
return v___x_4304_;
}
}
}
else
{
uint8_t v___x_4312_; 
lean_dec(v_alt_4298_);
v___x_4312_ = 0;
return v___x_4312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4313_, lean_object* v___x_4314_, lean_object* v_as_4315_, lean_object* v_i_4316_, lean_object* v_stop_4317_){
_start:
{
uint8_t v___x_358__boxed_4318_; size_t v_i_boxed_4319_; size_t v_stop_boxed_4320_; uint8_t v_res_4321_; lean_object* v_r_4322_; 
v___x_358__boxed_4318_ = lean_unbox(v___x_4314_);
v_i_boxed_4319_ = lean_unbox_usize(v_i_4316_);
lean_dec(v_i_4316_);
v_stop_boxed_4320_ = lean_unbox_usize(v_stop_4317_);
lean_dec(v_stop_4317_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4313_, v___x_358__boxed_4318_, v_as_4315_, v_i_boxed_4319_, v_stop_boxed_4320_);
lean_dec_ref(v_as_4315_);
v_r_4322_ = lean_box(v_res_4321_);
return v_r_4322_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4323_){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = lean_array_get_size(v_alts_4323_);
v___x_4326_ = lean_nat_dec_lt(v___x_4324_, v___x_4325_);
if (v___x_4326_ == 0)
{
uint8_t v___x_4327_; 
v___x_4327_ = 1;
return v___x_4327_;
}
else
{
lean_object* v_alt_4328_; uint8_t v___x_4329_; 
v_alt_4328_ = lean_array_fget_borrowed(v_alts_4323_, v___x_4324_);
lean_inc(v_alt_4328_);
v___x_4329_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_alt_4328_);
if (v___x_4329_ == 0)
{
return v___x_4329_;
}
else
{
if (v___x_4326_ == 0)
{
return v___x_4329_;
}
else
{
if (v___x_4326_ == 0)
{
return v___x_4329_;
}
else
{
size_t v___x_4330_; size_t v___x_4331_; uint8_t v___x_4332_; 
v___x_4330_ = ((size_t)0ULL);
v___x_4331_ = lean_usize_of_nat(v___x_4325_);
lean_inc(v_alt_4328_);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4328_, v___x_4329_, v_alts_4323_, v___x_4330_, v___x_4331_);
if (v___x_4332_ == 0)
{
return v___x_4329_;
}
else
{
uint8_t v___x_4333_; 
v___x_4333_ = 0;
return v___x_4333_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4334_){
_start:
{
uint8_t v_res_4335_; lean_object* v_r_4336_; 
v_res_4335_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4334_);
lean_dec_ref(v_alts_4334_);
v_r_4336_ = lean_box(v_res_4335_);
return v_r_4336_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4344_){
_start:
{
if (lean_obj_tag(v_alt_4344_) == 1)
{
lean_object* v_tail_4345_; 
v_tail_4345_ = lean_ctor_get(v_alt_4344_, 1);
if (lean_obj_tag(v_tail_4345_) == 0)
{
lean_object* v_head_4346_; lean_object* v___x_4347_; uint8_t v___x_4348_; 
v_head_4346_ = lean_ctor_get(v_alt_4344_, 0);
lean_inc(v_head_4346_);
lean_dec_ref(v_alt_4344_);
v___x_4347_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4348_ = l_Lean_Syntax_isOfKind(v_head_4346_, v___x_4347_);
return v___x_4348_;
}
else
{
uint8_t v___x_4349_; 
lean_dec_ref(v_alt_4344_);
v___x_4349_ = 0;
return v___x_4349_;
}
}
else
{
uint8_t v___x_4350_; 
lean_dec(v_alt_4344_);
v___x_4350_ = 0;
return v___x_4350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4351_){
_start:
{
uint8_t v_res_4352_; lean_object* v_r_4353_; 
v_res_4352_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4351_);
v_r_4353_ = lean_box(v_res_4352_);
return v_r_4353_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4354_, lean_object* v_x_4355_, lean_object* v___y_4356_){
_start:
{
if (lean_obj_tag(v_x_4354_) == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = l_List_reverse___redArg(v_x_4355_);
v___x_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
return v___x_4359_;
}
else
{
lean_object* v_head_4360_; lean_object* v_tail_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4379_; 
v_head_4360_ = lean_ctor_get(v_x_4354_, 0);
v_tail_4361_ = lean_ctor_get(v_x_4354_, 1);
v_isSharedCheck_4379_ = !lean_is_exclusive(v_x_4354_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4363_ = v_x_4354_;
v_isShared_4364_ = v_isSharedCheck_4379_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_tail_4361_);
lean_inc(v_head_4360_);
lean_dec(v_x_4354_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4379_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4360_, v___y_4356_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref(v___x_4365_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 1, v_x_4355_);
lean_ctor_set(v___x_4363_, 0, v_a_4366_);
v___x_4368_ = v___x_4363_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4366_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_x_4355_);
v___x_4368_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
v_x_4354_ = v_tail_4361_;
v_x_4355_ = v___x_4368_;
goto _start;
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_del_object(v___x_4363_);
lean_dec(v_tail_4361_);
lean_dec(v_x_4355_);
v_a_4371_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4365_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4365_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4380_, lean_object* v_x_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4380_, v_x_4381_, v___y_4382_);
lean_dec_ref(v___y_4382_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4385_, lean_object* v_alts_4386_, uint8_t v_compress_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_seq_4392_; 
if (v_compress_4387_ == 0)
{
goto v___jp_4395_;
}
else
{
uint8_t v___x_4405_; 
v___x_4405_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4386_);
if (v___x_4405_ == 0)
{
goto v___jp_4395_;
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = lean_array_get_size(v_alts_4386_);
v___x_4408_ = lean_nat_dec_lt(v___x_4406_, v___x_4407_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec_ref(v_alts_4386_);
v___x_4409_ = lean_box(0);
v___x_4410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4410_, 0, v_cases_4385_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
return v___x_4411_;
}
else
{
lean_object* v___x_4412_; lean_object* v_firstAlt_4413_; uint8_t v___x_4414_; 
v___x_4412_ = lean_box(0);
v_firstAlt_4413_ = lean_array_get(v___x_4412_, v_alts_4386_, v___x_4406_);
lean_dec_ref(v_alts_4386_);
lean_inc(v_firstAlt_4413_);
v___x_4414_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4413_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4415_; lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4424_; 
v___x_4415_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4385_, v_firstAlt_4413_, v_a_4388_);
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4424_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4424_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4420_, 0, v_a_4416_);
lean_ctor_set(v___x_4420_, 1, v___x_4412_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4420_);
v___x_4422_ = v___x_4418_;
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
else
{
lean_object* v___x_4425_; 
lean_dec(v_cases_4385_);
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v_firstAlt_4413_);
return v___x_4425_;
}
}
}
}
v___jp_4391_:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_cases_4385_);
lean_ctor_set(v___x_4393_, 1, v_seq_4392_);
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
return v___x_4394_;
}
v___jp_4395_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4396_ = lean_array_get_size(v_alts_4386_);
v___x_4397_ = lean_unsigned_to_nat(1u);
v___x_4398_ = lean_nat_dec_eq(v___x_4396_, v___x_4397_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4399_ = lean_array_to_list(v_alts_4386_);
v___x_4400_ = lean_box(0);
v___x_4401_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4399_, v___x_4400_, v_a_4388_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref(v___x_4401_);
v_seq_4392_ = v_a_4402_;
goto v___jp_4391_;
}
else
{
lean_dec(v_cases_4385_);
return v___x_4401_;
}
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_unsigned_to_nat(0u);
v___x_4404_ = lean_array_fget(v_alts_4386_, v___x_4403_);
lean_dec_ref(v_alts_4386_);
v_seq_4392_ = v___x_4404_;
goto v___jp_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4426_, lean_object* v_alts_4427_, lean_object* v_compress_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
uint8_t v_compress_boxed_4432_; lean_object* v_res_4433_; 
v_compress_boxed_4432_ = lean_unbox(v_compress_4428_);
v_res_4433_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4426_, v_alts_4427_, v_compress_boxed_4432_, v_a_4429_, v_a_4430_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4434_, v_x_4435_, v___y_4436_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4440_, lean_object* v_x_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4440_, v_x_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___x_4449_; lean_object* v_env_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4449_ = lean_st_ref_get(v___y_4447_);
v_env_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc_ref(v_env_4450_);
lean_dec(v___x_4449_);
v___x_4451_ = l_Lean_Meta_isMatcherAppCore(v_env_4450_, v_e_4446_);
v___x_4452_ = lean_box(v___x_4451_);
v___x_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v_e_4454_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4458_, v___y_4468_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v_e_4471_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_apply_10(v_x_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, lean_box(0));
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4508_, lean_object* v_x_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v___f_4520_; lean_object* v___x_4521_; 
v___f_4520_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4520_, 0, v_x_4509_);
lean_closure_set(v___f_4520_, 1, v___y_4510_);
lean_closure_set(v___f_4520_, 2, v___y_4511_);
lean_closure_set(v___f_4520_, 3, v___y_4512_);
lean_closure_set(v___f_4520_, 4, v___y_4513_);
lean_closure_set(v___f_4520_, 5, v___y_4514_);
v___x_4521_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4508_, v___f_4520_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
if (lean_obj_tag(v___x_4521_) == 0)
{
return v___x_4521_;
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4521_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4521_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_4530_, lean_object* v_x_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4530_, v_x_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_4543_, lean_object* v_mvarId_4544_, lean_object* v_x_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4544_, v_x_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_4557_, lean_object* v_mvarId_4558_, lean_object* v_x_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_4557_, v_mvarId_4558_, v_x_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v___x_4574_; 
v___x_4574_ = l_Lean_Expr_hasMVar(v_e_4571_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; 
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v_e_4571_);
return v___x_4575_;
}
else
{
lean_object* v___x_4576_; lean_object* v_mctx_4577_; lean_object* v___x_4578_; lean_object* v_fst_4579_; lean_object* v_snd_4580_; lean_object* v___x_4581_; lean_object* v_cache_4582_; lean_object* v_zetaDeltaFVarIds_4583_; lean_object* v_postponed_4584_; lean_object* v_diag_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4594_; 
v___x_4576_ = lean_st_ref_get(v___y_4572_);
v_mctx_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc_ref(v_mctx_4577_);
lean_dec(v___x_4576_);
v___x_4578_ = l_Lean_instantiateMVarsCore(v_mctx_4577_, v_e_4571_);
v_fst_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_fst_4579_);
v_snd_4580_ = lean_ctor_get(v___x_4578_, 1);
lean_inc(v_snd_4580_);
lean_dec_ref(v___x_4578_);
v___x_4581_ = lean_st_ref_take(v___y_4572_);
v_cache_4582_ = lean_ctor_get(v___x_4581_, 1);
v_zetaDeltaFVarIds_4583_ = lean_ctor_get(v___x_4581_, 2);
v_postponed_4584_ = lean_ctor_get(v___x_4581_, 3);
v_diag_4585_ = lean_ctor_get(v___x_4581_, 4);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4581_, 0);
lean_dec(v_unused_4595_);
v___x_4587_ = v___x_4581_;
v_isShared_4588_ = v_isSharedCheck_4594_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_diag_4585_);
lean_inc(v_postponed_4584_);
lean_inc(v_zetaDeltaFVarIds_4583_);
lean_inc(v_cache_4582_);
lean_dec(v___x_4581_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4594_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 0, v_snd_4580_);
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_snd_4580_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_cache_4582_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_zetaDeltaFVarIds_4583_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_postponed_4584_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_diag_4585_);
v___x_4590_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = lean_st_ref_set(v___y_4572_, v___x_4590_);
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_fst_4579_);
return v___x_4592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_4596_, v___y_4597_);
lean_dec(v___y_4597_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; 
v___x_4611_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_4600_, v___y_4607_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(uint8_t v___x_4624_, lean_object* v_x_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = lean_box(v___x_4624_);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object* v___x_4639_, lean_object* v_x_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
uint8_t v___x_86972__boxed_4652_; lean_object* v_res_4653_; 
v___x_86972__boxed_4652_ = lean_unbox(v___x_4639_);
v_res_4653_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_86972__boxed_4652_, v_x_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v_x_4640_);
return v_res_4653_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__0));
v___x_4656_ = l_Lean_stringToMessageData(v___x_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_4660_, lean_object* v___x_4661_, uint8_t v_trace_4662_, lean_object* v_c_4663_, lean_object* v_a_4664_, lean_object* v_numCases_4665_, uint8_t v_isRec_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___x_4677_; lean_object* v___y_4679_; lean_object* v_numDigits_4680_; lean_object* v___y_4686_; lean_object* v_mvarIds_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___x_4768_; 
v___x_4677_ = lean_st_mk_ref(v_goal_4660_);
v___x_4768_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_4661_, v___x_4677_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v___x_4827_; uint8_t v___y_4829_; uint8_t v___x_4832_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref(v___x_4768_);
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4832_ = lean_nat_dec_lt(v___x_4827_, v_numCases_4665_);
if (v___x_4832_ == 0)
{
v___y_4829_ = v_isRec_4666_;
goto v___jp_4828_;
}
else
{
v___y_4829_ = v___x_4832_;
goto v___jp_4828_;
}
v___jp_4770_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_4663_);
lean_inc_ref(v___x_4661_);
v___x_4774_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_4661_, v___y_4772_, v_numCases_4665_, v___x_4773_, v___y_4669_, v___y_4672_, v___y_4674_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v___x_4775_; 
lean_dec_ref(v___x_4774_);
lean_inc_ref(v___x_4661_);
v___x_4775_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_4661_, v___x_4677_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4810_; 
lean_dec_ref(v___x_4775_);
v___x_4776_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1));
v___x_4777_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_4776_, v___y_4674_);
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4810_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4810_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
uint8_t v___x_4782_; 
v___x_4782_ = lean_unbox(v_a_4778_);
lean_dec(v_a_4778_);
if (v___x_4782_ == 0)
{
lean_del_object(v___x_4780_);
lean_dec(v_a_4769_);
lean_inc(v___x_4677_);
v___y_4711_ = v___y_4771_;
v___y_4712_ = v___x_4677_;
v___y_4713_ = v___y_4667_;
v___y_4714_ = v___y_4668_;
v___y_4715_ = v___y_4669_;
v___y_4716_ = v___y_4670_;
v___y_4717_ = v___y_4671_;
v___y_4718_ = v___y_4672_;
v___y_4719_ = v___y_4673_;
v___y_4720_ = v___y_4674_;
v___y_4721_ = v___y_4675_;
goto v___jp_4710_;
}
else
{
lean_object* v___x_4783_; 
v___x_4783_ = l_Lean_Meta_Grind_updateLastTag(v___x_4677_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4789_; 
lean_dec_ref(v___x_4783_);
lean_inc_ref(v___x_4661_);
v___x_4784_ = l_Lean_MessageData_ofExpr(v___x_4661_);
v___x_4785_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1);
v___x_4786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4784_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
v___x_4787_ = l_Nat_reprFast(v_a_4769_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set_tag(v___x_4780_, 3);
lean_ctor_set(v___x_4780_, 0, v___x_4787_);
v___x_4789_ = v___x_4780_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4790_ = l_Lean_MessageData_ofFormat(v___x_4789_);
v___x_4791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4786_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
v___x_4792_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__2___redArg(v___x_4776_, v___x_4791_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_dec_ref(v___x_4792_);
lean_inc(v___x_4677_);
v___y_4711_ = v___y_4771_;
v___y_4712_ = v___x_4677_;
v___y_4713_ = v___y_4667_;
v___y_4714_ = v___y_4668_;
v___y_4715_ = v___y_4669_;
v___y_4716_ = v___y_4670_;
v___y_4717_ = v___y_4671_;
v___y_4718_ = v___y_4672_;
v___y_4719_ = v___y_4673_;
v___y_4720_ = v___y_4674_;
v___y_4721_ = v___y_4675_;
goto v___jp_4710_;
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec_ref(v___y_4771_);
lean_dec(v___x_4677_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec(v_a_4664_);
lean_dec_ref(v_c_4663_);
lean_dec_ref(v___x_4661_);
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4792_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_del_object(v___x_4780_);
lean_dec_ref(v___y_4771_);
lean_dec(v_a_4769_);
lean_dec(v___x_4677_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec(v_a_4664_);
lean_dec_ref(v_c_4663_);
lean_dec_ref(v___x_4661_);
v_a_4802_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4783_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4783_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec_ref(v___y_4771_);
lean_dec(v_a_4769_);
lean_dec(v___x_4677_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec(v_a_4664_);
lean_dec_ref(v_c_4663_);
lean_dec_ref(v___x_4661_);
v_a_4811_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4775_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4775_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec_ref(v___y_4771_);
lean_dec(v_a_4769_);
lean_dec(v___x_4677_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec(v_a_4664_);
lean_dec_ref(v_c_4663_);
lean_dec_ref(v___x_4661_);
v_a_4819_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4774_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4774_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
v___jp_4828_:
{
lean_object* v___f_4830_; 
v___f_4830_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__2));
if (v___y_4829_ == 0)
{
lean_inc(v_a_4769_);
v___y_4771_ = v___f_4830_;
v___y_4772_ = v_a_4769_;
goto v___jp_4770_;
}
else
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_nat_add(v_a_4769_, v___x_4827_);
v___y_4771_ = v___f_4830_;
v___y_4772_ = v___x_4831_;
goto v___jp_4770_;
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec(v___x_4677_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec(v_numCases_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_c_4663_);
lean_dec_ref(v___x_4661_);
v_a_4833_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4768_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4768_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
v___jp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4681_ = lean_st_ref_get(v___x_4677_);
lean_dec(v___x_4677_);
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v___y_4679_);
lean_ctor_set(v___x_4682_, 1, v_numDigits_4680_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
lean_ctor_set(v___x_4683_, 1, v___x_4681_);
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
return v___x_4684_;
}
v___jp_4685_:
{
if (v_trace_4662_ == 0)
{
lean_object* v___x_4698_; 
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4686_);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___y_4679_ = v_mvarIds_4687_;
v_numDigits_4680_ = v___x_4698_;
goto v___jp_4678_;
}
else
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___y_4686_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v_numDigits_4701_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref(v___x_4699_);
v_numDigits_4701_ = lean_ctor_get(v_a_4700_, 1);
lean_inc(v_numDigits_4701_);
lean_dec(v_a_4700_);
v___y_4679_ = v_mvarIds_4687_;
v_numDigits_4680_ = v_numDigits_4701_;
goto v___jp_4678_;
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec(v_mvarIds_4687_);
lean_dec(v___x_4677_);
v_a_4702_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4699_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4699_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
v___jp_4710_:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_4661_, v___y_4721_);
if (lean_obj_tag(v_c_4663_) == 1)
{
lean_object* v_e_4723_; lean_object* v_binderType_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
lean_dec_ref(v___x_4722_);
lean_dec_ref(v___x_4661_);
v_e_4723_ = lean_ctor_get(v_c_4663_, 0);
lean_inc_ref(v_e_4723_);
lean_dec_ref(v_c_4663_);
v_binderType_4724_ = lean_ctor_get(v_e_4723_, 1);
lean_inc_ref(v_binderType_4724_);
lean_dec_ref(v_e_4723_);
v___x_4725_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_4724_);
lean_inc(v___y_4721_);
lean_inc_ref(v___y_4720_);
lean_inc(v___y_4719_);
lean_inc_ref(v___y_4718_);
v___x_4726_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_4664_, v___x_4725_, v___y_4714_, v___y_4715_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref(v___x_4726_);
v___y_4686_ = v___y_4711_;
v_mvarIds_4687_ = v_a_4727_;
v___y_4688_ = v___y_4712_;
v___y_4689_ = v___y_4713_;
v___y_4690_ = v___y_4714_;
v___y_4691_ = v___y_4715_;
v___y_4692_ = v___y_4716_;
v___y_4693_ = v___y_4717_;
v___y_4694_ = v___y_4718_;
v___y_4695_ = v___y_4719_;
v___y_4696_ = v___y_4720_;
v___y_4697_ = v___y_4721_;
goto v___jp_4685_;
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4677_);
v_a_4728_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4726_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4726_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
else
{
lean_object* v_a_4736_; uint8_t v___x_4737_; 
lean_dec_ref(v_c_4663_);
v_a_4736_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4736_);
lean_dec_ref(v___x_4722_);
v___x_4737_ = lean_unbox(v_a_4736_);
lean_dec(v_a_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; 
lean_inc(v___y_4721_);
lean_inc_ref(v___y_4720_);
lean_inc(v___y_4719_);
lean_inc_ref(v___y_4718_);
lean_inc(v___y_4717_);
lean_inc_ref(v___y_4716_);
lean_inc(v___y_4715_);
lean_inc_ref(v___y_4714_);
lean_inc(v___y_4713_);
lean_inc(v___y_4712_);
v___x_4738_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_4661_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; lean_object* v___x_4740_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc(v_a_4739_);
lean_dec_ref(v___x_4738_);
lean_inc(v___y_4721_);
lean_inc_ref(v___y_4720_);
lean_inc(v___y_4719_);
lean_inc_ref(v___y_4718_);
v___x_4740_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_4664_, v_a_4739_, v___y_4714_, v___y_4715_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4740_);
v___y_4686_ = v___y_4711_;
v_mvarIds_4687_ = v_a_4741_;
v___y_4688_ = v___y_4712_;
v___y_4689_ = v___y_4713_;
v___y_4690_ = v___y_4714_;
v___y_4691_ = v___y_4715_;
v___y_4692_ = v___y_4716_;
v___y_4693_ = v___y_4717_;
v___y_4694_ = v___y_4718_;
v___y_4695_ = v___y_4719_;
v___y_4696_ = v___y_4720_;
v___y_4697_ = v___y_4721_;
goto v___jp_4685_;
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4677_);
v_a_4742_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4740_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4740_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4677_);
lean_dec(v_a_4664_);
v_a_4750_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4738_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4738_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
else
{
lean_object* v___x_4758_; 
lean_inc(v___y_4721_);
lean_inc_ref(v___y_4720_);
lean_inc(v___y_4719_);
lean_inc_ref(v___y_4718_);
v___x_4758_ = l_Lean_Meta_Grind_casesMatch(v_a_4664_, v___x_4661_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref(v___x_4758_);
v___y_4686_ = v___y_4711_;
v_mvarIds_4687_ = v_a_4759_;
v___y_4688_ = v___y_4712_;
v___y_4689_ = v___y_4713_;
v___y_4690_ = v___y_4714_;
v___y_4691_ = v___y_4715_;
v___y_4692_ = v___y_4716_;
v___y_4693_ = v___y_4717_;
v___y_4694_ = v___y_4718_;
v___y_4695_ = v___y_4719_;
v___y_4696_ = v___y_4720_;
v___y_4697_ = v___y_4721_;
goto v___jp_4685_;
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4677_);
v_a_4760_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4758_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4758_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_goal_4841_ = _args[0];
lean_object* v___x_4842_ = _args[1];
lean_object* v_trace_4843_ = _args[2];
lean_object* v_c_4844_ = _args[3];
lean_object* v_a_4845_ = _args[4];
lean_object* v_numCases_4846_ = _args[5];
lean_object* v_isRec_4847_ = _args[6];
lean_object* v___y_4848_ = _args[7];
lean_object* v___y_4849_ = _args[8];
lean_object* v___y_4850_ = _args[9];
lean_object* v___y_4851_ = _args[10];
lean_object* v___y_4852_ = _args[11];
lean_object* v___y_4853_ = _args[12];
lean_object* v___y_4854_ = _args[13];
lean_object* v___y_4855_ = _args[14];
lean_object* v___y_4856_ = _args[15];
lean_object* v___y_4857_ = _args[16];
_start:
{
uint8_t v_trace_boxed_4858_; uint8_t v_isRec_boxed_4859_; lean_object* v_res_4860_; 
v_trace_boxed_4858_ = lean_unbox(v_trace_4843_);
v_isRec_boxed_4859_ = lean_unbox(v_isRec_4847_);
v_res_4860_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_4841_, v___x_4842_, v_trace_boxed_4858_, v_c_4844_, v_a_4845_, v_numCases_4846_, v_isRec_boxed_4859_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_4861_, lean_object* v_x_4862_, lean_object* v_x_4863_, lean_object* v_x_4864_){
_start:
{
lean_object* v_ks_4865_; lean_object* v_vs_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4890_; 
v_ks_4865_ = lean_ctor_get(v_x_4861_, 0);
v_vs_4866_ = lean_ctor_get(v_x_4861_, 1);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_x_4861_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4868_ = v_x_4861_;
v_isShared_4869_ = v_isSharedCheck_4890_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_vs_4866_);
lean_inc(v_ks_4865_);
lean_dec(v_x_4861_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4890_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4870_; uint8_t v___x_4871_; 
v___x_4870_ = lean_array_get_size(v_ks_4865_);
v___x_4871_ = lean_nat_dec_lt(v_x_4862_, v___x_4870_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4875_; 
lean_dec(v_x_4862_);
v___x_4872_ = lean_array_push(v_ks_4865_, v_x_4863_);
v___x_4873_ = lean_array_push(v_vs_4866_, v_x_4864_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 1, v___x_4873_);
lean_ctor_set(v___x_4868_, 0, v___x_4872_);
v___x_4875_ = v___x_4868_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4872_);
lean_ctor_set(v_reuseFailAlloc_4876_, 1, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
else
{
lean_object* v_k_x27_4877_; uint8_t v___x_4878_; 
v_k_x27_4877_ = lean_array_fget_borrowed(v_ks_4865_, v_x_4862_);
v___x_4878_ = l_Lean_instBEqMVarId_beq(v_x_4863_, v_k_x27_4877_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4880_; 
if (v_isShared_4869_ == 0)
{
v___x_4880_ = v___x_4868_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_ks_4865_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_vs_4866_);
v___x_4880_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = lean_unsigned_to_nat(1u);
v___x_4882_ = lean_nat_add(v_x_4862_, v___x_4881_);
lean_dec(v_x_4862_);
v_x_4861_ = v___x_4880_;
v_x_4862_ = v___x_4882_;
goto _start;
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4885_ = lean_array_fset(v_ks_4865_, v_x_4862_, v_x_4863_);
v___x_4886_ = lean_array_fset(v_vs_4866_, v_x_4862_, v_x_4864_);
lean_dec(v_x_4862_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 1, v___x_4886_);
lean_ctor_set(v___x_4868_, 0, v___x_4885_);
v___x_4888_ = v___x_4868_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_4891_, lean_object* v_k_4892_, lean_object* v_v_4893_){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = lean_unsigned_to_nat(0u);
v___x_4895_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_4891_, v___x_4894_, v_k_4892_, v_v_4893_);
return v___x_4895_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_4896_; size_t v___x_4897_; size_t v___x_4898_; 
v___x_4896_ = ((size_t)5ULL);
v___x_4897_ = ((size_t)1ULL);
v___x_4898_ = lean_usize_shift_left(v___x_4897_, v___x_4896_);
return v___x_4898_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_4899_; size_t v___x_4900_; size_t v___x_4901_; 
v___x_4899_ = ((size_t)1ULL);
v___x_4900_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_4901_ = lean_usize_sub(v___x_4900_, v___x_4899_);
return v___x_4901_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_4903_, size_t v_x_4904_, size_t v_x_4905_, lean_object* v_x_4906_, lean_object* v_x_4907_){
_start:
{
if (lean_obj_tag(v_x_4903_) == 0)
{
lean_object* v_es_4908_; size_t v___x_4909_; size_t v___x_4910_; size_t v___x_4911_; size_t v___x_4912_; lean_object* v_j_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; 
v_es_4908_ = lean_ctor_get(v_x_4903_, 0);
v___x_4909_ = ((size_t)5ULL);
v___x_4910_ = ((size_t)1ULL);
v___x_4911_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1);
v___x_4912_ = lean_usize_land(v_x_4904_, v___x_4911_);
v_j_4913_ = lean_usize_to_nat(v___x_4912_);
v___x_4914_ = lean_array_get_size(v_es_4908_);
v___x_4915_ = lean_nat_dec_lt(v_j_4913_, v___x_4914_);
if (v___x_4915_ == 0)
{
lean_dec(v_j_4913_);
lean_dec(v_x_4907_);
lean_dec(v_x_4906_);
return v_x_4903_;
}
else
{
lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4952_; 
lean_inc_ref(v_es_4908_);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_x_4903_);
if (v_isSharedCheck_4952_ == 0)
{
lean_object* v_unused_4953_; 
v_unused_4953_ = lean_ctor_get(v_x_4903_, 0);
lean_dec(v_unused_4953_);
v___x_4917_ = v_x_4903_;
v_isShared_4918_ = v_isSharedCheck_4952_;
goto v_resetjp_4916_;
}
else
{
lean_dec(v_x_4903_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4952_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v_v_4919_; lean_object* v___x_4920_; lean_object* v_xs_x27_4921_; lean_object* v___y_4923_; 
v_v_4919_ = lean_array_fget(v_es_4908_, v_j_4913_);
v___x_4920_ = lean_box(0);
v_xs_x27_4921_ = lean_array_fset(v_es_4908_, v_j_4913_, v___x_4920_);
switch(lean_obj_tag(v_v_4919_))
{
case 0:
{
lean_object* v_key_4928_; lean_object* v_val_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4939_; 
v_key_4928_ = lean_ctor_get(v_v_4919_, 0);
v_val_4929_ = lean_ctor_get(v_v_4919_, 1);
v_isSharedCheck_4939_ = !lean_is_exclusive(v_v_4919_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4931_ = v_v_4919_;
v_isShared_4932_ = v_isSharedCheck_4939_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_val_4929_);
lean_inc(v_key_4928_);
lean_dec(v_v_4919_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4939_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
uint8_t v___x_4933_; 
v___x_4933_ = l_Lean_instBEqMVarId_beq(v_x_4906_, v_key_4928_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_del_object(v___x_4931_);
v___x_4934_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4928_, v_val_4929_, v_x_4906_, v_x_4907_);
v___x_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
v___y_4923_ = v___x_4935_;
goto v___jp_4922_;
}
else
{
lean_object* v___x_4937_; 
lean_dec(v_val_4929_);
lean_dec(v_key_4928_);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 1, v_x_4907_);
lean_ctor_set(v___x_4931_, 0, v_x_4906_);
v___x_4937_ = v___x_4931_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_x_4906_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v_x_4907_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
v___y_4923_ = v___x_4937_;
goto v___jp_4922_;
}
}
}
}
case 1:
{
lean_object* v_node_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4950_; 
v_node_4940_ = lean_ctor_get(v_v_4919_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_v_4919_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4942_ = v_v_4919_;
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_node_4940_);
lean_dec(v_v_4919_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
size_t v___x_4944_; size_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4944_ = lean_usize_shift_right(v_x_4904_, v___x_4909_);
v___x_4945_ = lean_usize_add(v_x_4905_, v___x_4910_);
v___x_4946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_4940_, v___x_4944_, v___x_4945_, v_x_4906_, v_x_4907_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 0, v___x_4946_);
v___x_4948_ = v___x_4942_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
v___y_4923_ = v___x_4948_;
goto v___jp_4922_;
}
}
}
default: 
{
lean_object* v___x_4951_; 
v___x_4951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4951_, 0, v_x_4906_);
lean_ctor_set(v___x_4951_, 1, v_x_4907_);
v___y_4923_ = v___x_4951_;
goto v___jp_4922_;
}
}
v___jp_4922_:
{
lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4924_ = lean_array_fset(v_xs_x27_4921_, v_j_4913_, v___y_4923_);
lean_dec(v_j_4913_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4924_);
v___x_4926_ = v___x_4917_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
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
else
{
lean_object* v_ks_4954_; lean_object* v_vs_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4975_; 
v_ks_4954_ = lean_ctor_get(v_x_4903_, 0);
v_vs_4955_ = lean_ctor_get(v_x_4903_, 1);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_x_4903_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4957_ = v_x_4903_;
v_isShared_4958_ = v_isSharedCheck_4975_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_vs_4955_);
lean_inc(v_ks_4954_);
lean_dec(v_x_4903_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4975_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_ks_4954_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_vs_4955_);
v___x_4960_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
lean_object* v_newNode_4961_; uint8_t v___y_4963_; size_t v___x_4969_; uint8_t v___x_4970_; 
v_newNode_4961_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_4960_, v_x_4906_, v_x_4907_);
v___x_4969_ = ((size_t)7ULL);
v___x_4970_ = lean_usize_dec_le(v___x_4969_, v_x_4905_);
if (v___x_4970_ == 0)
{
lean_object* v___x_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; 
v___x_4971_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4961_);
v___x_4972_ = lean_unsigned_to_nat(4u);
v___x_4973_ = lean_nat_dec_lt(v___x_4971_, v___x_4972_);
lean_dec(v___x_4971_);
v___y_4963_ = v___x_4973_;
goto v___jp_4962_;
}
else
{
v___y_4963_ = v___x_4970_;
goto v___jp_4962_;
}
v___jp_4962_:
{
if (v___y_4963_ == 0)
{
lean_object* v_ks_4964_; lean_object* v_vs_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_ks_4964_ = lean_ctor_get(v_newNode_4961_, 0);
lean_inc_ref(v_ks_4964_);
v_vs_4965_ = lean_ctor_get(v_newNode_4961_, 1);
lean_inc_ref(v_vs_4965_);
lean_dec_ref(v_newNode_4961_);
v___x_4966_ = lean_unsigned_to_nat(0u);
v___x_4967_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2);
v___x_4968_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_4905_, v_ks_4964_, v_vs_4965_, v___x_4966_, v___x_4967_);
lean_dec_ref(v_vs_4965_);
lean_dec_ref(v_ks_4964_);
return v___x_4968_;
}
else
{
return v_newNode_4961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_4976_, lean_object* v_keys_4977_, lean_object* v_vals_4978_, lean_object* v_i_4979_, lean_object* v_entries_4980_){
_start:
{
lean_object* v___x_4981_; uint8_t v___x_4982_; 
v___x_4981_ = lean_array_get_size(v_keys_4977_);
v___x_4982_ = lean_nat_dec_lt(v_i_4979_, v___x_4981_);
if (v___x_4982_ == 0)
{
lean_dec(v_i_4979_);
return v_entries_4980_;
}
else
{
lean_object* v_k_4983_; lean_object* v_v_4984_; uint64_t v___x_4985_; size_t v_h_4986_; size_t v___x_4987_; lean_object* v___x_4988_; size_t v___x_4989_; size_t v___x_4990_; size_t v___x_4991_; size_t v_h_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_k_4983_ = lean_array_fget_borrowed(v_keys_4977_, v_i_4979_);
v_v_4984_ = lean_array_fget_borrowed(v_vals_4978_, v_i_4979_);
v___x_4985_ = l_Lean_instHashableMVarId_hash(v_k_4983_);
v_h_4986_ = lean_uint64_to_usize(v___x_4985_);
v___x_4987_ = ((size_t)5ULL);
v___x_4988_ = lean_unsigned_to_nat(1u);
v___x_4989_ = ((size_t)1ULL);
v___x_4990_ = lean_usize_sub(v_depth_4976_, v___x_4989_);
v___x_4991_ = lean_usize_mul(v___x_4987_, v___x_4990_);
v_h_4992_ = lean_usize_shift_right(v_h_4986_, v___x_4991_);
v___x_4993_ = lean_nat_add(v_i_4979_, v___x_4988_);
lean_dec(v_i_4979_);
lean_inc(v_v_4984_);
lean_inc(v_k_4983_);
v___x_4994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_4980_, v_h_4992_, v_depth_4976_, v_k_4983_, v_v_4984_);
v_i_4979_ = v___x_4993_;
v_entries_4980_ = v___x_4994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_4996_, lean_object* v_keys_4997_, lean_object* v_vals_4998_, lean_object* v_i_4999_, lean_object* v_entries_5000_){
_start:
{
size_t v_depth_boxed_5001_; lean_object* v_res_5002_; 
v_depth_boxed_5001_ = lean_unbox_usize(v_depth_4996_);
lean_dec(v_depth_4996_);
v_res_5002_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5001_, v_keys_4997_, v_vals_4998_, v_i_4999_, v_entries_5000_);
lean_dec_ref(v_vals_4998_);
lean_dec_ref(v_keys_4997_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5003_, lean_object* v_x_5004_, lean_object* v_x_5005_, lean_object* v_x_5006_, lean_object* v_x_5007_){
_start:
{
size_t v_x_87493__boxed_5008_; size_t v_x_87494__boxed_5009_; lean_object* v_res_5010_; 
v_x_87493__boxed_5008_ = lean_unbox_usize(v_x_5004_);
lean_dec(v_x_5004_);
v_x_87494__boxed_5009_ = lean_unbox_usize(v_x_5005_);
lean_dec(v_x_5005_);
v_res_5010_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5003_, v_x_87493__boxed_5008_, v_x_87494__boxed_5009_, v_x_5006_, v_x_5007_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5011_, lean_object* v_x_5012_, lean_object* v_x_5013_){
_start:
{
uint64_t v___x_5014_; size_t v___x_5015_; size_t v___x_5016_; lean_object* v___x_5017_; 
v___x_5014_ = l_Lean_instHashableMVarId_hash(v_x_5012_);
v___x_5015_ = lean_uint64_to_usize(v___x_5014_);
v___x_5016_ = ((size_t)1ULL);
v___x_5017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5011_, v___x_5015_, v___x_5016_, v_x_5012_, v_x_5013_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5018_, lean_object* v_val_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; lean_object* v_mctx_5023_; lean_object* v_cache_5024_; lean_object* v_zetaDeltaFVarIds_5025_; lean_object* v_postponed_5026_; lean_object* v_diag_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5054_; 
v___x_5022_ = lean_st_ref_take(v___y_5020_);
v_mctx_5023_ = lean_ctor_get(v___x_5022_, 0);
v_cache_5024_ = lean_ctor_get(v___x_5022_, 1);
v_zetaDeltaFVarIds_5025_ = lean_ctor_get(v___x_5022_, 2);
v_postponed_5026_ = lean_ctor_get(v___x_5022_, 3);
v_diag_5027_ = lean_ctor_get(v___x_5022_, 4);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5029_ = v___x_5022_;
v_isShared_5030_ = v_isSharedCheck_5054_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_diag_5027_);
lean_inc(v_postponed_5026_);
lean_inc(v_zetaDeltaFVarIds_5025_);
lean_inc(v_cache_5024_);
lean_inc(v_mctx_5023_);
lean_dec(v___x_5022_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5054_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v_depth_5031_; lean_object* v_levelAssignDepth_5032_; lean_object* v_mvarCounter_5033_; lean_object* v_lDepth_5034_; lean_object* v_decls_5035_; lean_object* v_userNames_5036_; lean_object* v_lAssignment_5037_; lean_object* v_eAssignment_5038_; lean_object* v_dAssignment_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5053_; 
v_depth_5031_ = lean_ctor_get(v_mctx_5023_, 0);
v_levelAssignDepth_5032_ = lean_ctor_get(v_mctx_5023_, 1);
v_mvarCounter_5033_ = lean_ctor_get(v_mctx_5023_, 2);
v_lDepth_5034_ = lean_ctor_get(v_mctx_5023_, 3);
v_decls_5035_ = lean_ctor_get(v_mctx_5023_, 4);
v_userNames_5036_ = lean_ctor_get(v_mctx_5023_, 5);
v_lAssignment_5037_ = lean_ctor_get(v_mctx_5023_, 6);
v_eAssignment_5038_ = lean_ctor_get(v_mctx_5023_, 7);
v_dAssignment_5039_ = lean_ctor_get(v_mctx_5023_, 8);
v_isSharedCheck_5053_ = !lean_is_exclusive(v_mctx_5023_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5041_ = v_mctx_5023_;
v_isShared_5042_ = v_isSharedCheck_5053_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_dAssignment_5039_);
lean_inc(v_eAssignment_5038_);
lean_inc(v_lAssignment_5037_);
lean_inc(v_userNames_5036_);
lean_inc(v_decls_5035_);
lean_inc(v_lDepth_5034_);
lean_inc(v_mvarCounter_5033_);
lean_inc(v_levelAssignDepth_5032_);
lean_inc(v_depth_5031_);
lean_dec(v_mctx_5023_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5053_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5043_; lean_object* v___x_5045_; 
v___x_5043_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5038_, v_mvarId_5018_, v_val_5019_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 7, v___x_5043_);
v___x_5045_ = v___x_5041_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_depth_5031_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_levelAssignDepth_5032_);
lean_ctor_set(v_reuseFailAlloc_5052_, 2, v_mvarCounter_5033_);
lean_ctor_set(v_reuseFailAlloc_5052_, 3, v_lDepth_5034_);
lean_ctor_set(v_reuseFailAlloc_5052_, 4, v_decls_5035_);
lean_ctor_set(v_reuseFailAlloc_5052_, 5, v_userNames_5036_);
lean_ctor_set(v_reuseFailAlloc_5052_, 6, v_lAssignment_5037_);
lean_ctor_set(v_reuseFailAlloc_5052_, 7, v___x_5043_);
lean_ctor_set(v_reuseFailAlloc_5052_, 8, v_dAssignment_5039_);
v___x_5045_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5047_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5045_);
v___x_5047_ = v___x_5029_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v_cache_5024_);
lean_ctor_set(v_reuseFailAlloc_5051_, 2, v_zetaDeltaFVarIds_5025_);
lean_ctor_set(v_reuseFailAlloc_5051_, 3, v_postponed_5026_);
lean_ctor_set(v_reuseFailAlloc_5051_, 4, v_diag_5027_);
v___x_5047_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___x_5048_ = lean_st_ref_set(v___y_5020_, v___x_5047_);
v___x_5049_ = lean_box(0);
v___x_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5049_);
return v___x_5050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5055_, lean_object* v_val_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5055_, v_val_5056_, v___y_5057_);
lean_dec(v___y_5057_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5060_, lean_object* v_snd_5061_, uint8_t v_stopAtFirstFailure_5062_, lean_object* v_as_x27_5063_, lean_object* v_b_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
if (lean_obj_tag(v_as_x27_5063_) == 0)
{
lean_object* v___x_5075_; 
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v_snd_5061_);
lean_dec_ref(v_kp_5060_);
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v_b_5064_);
return v___x_5075_;
}
else
{
lean_object* v_head_5076_; lean_object* v_tail_5077_; lean_object* v___x_5078_; 
v_head_5076_ = lean_ctor_get(v_as_x27_5063_, 0);
lean_inc(v_head_5076_);
v_tail_5077_ = lean_ctor_get(v_as_x27_5063_, 1);
lean_inc(v_tail_5077_);
lean_dec_ref(v_as_x27_5063_);
lean_inc_ref(v_kp_5060_);
lean_inc(v___y_5073_);
lean_inc_ref(v___y_5072_);
lean_inc(v___y_5071_);
lean_inc_ref(v___y_5070_);
lean_inc(v___y_5069_);
lean_inc_ref(v___y_5068_);
lean_inc(v___y_5067_);
lean_inc_ref(v___y_5066_);
lean_inc(v___y_5065_);
lean_inc(v_head_5076_);
v___x_5078_ = lean_apply_11(v_kp_5060_, v_head_5076_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, lean_box(0));
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_snd_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5174_; 
v_snd_5079_ = lean_ctor_get(v_b_5064_, 1);
v_isSharedCheck_5174_ = !lean_is_exclusive(v_b_5064_);
if (v_isSharedCheck_5174_ == 0)
{
lean_object* v_unused_5175_; 
v_unused_5175_ = lean_ctor_get(v_b_5064_, 0);
lean_dec(v_unused_5175_);
v___x_5081_ = v_b_5064_;
v_isShared_5082_ = v_isSharedCheck_5174_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_snd_5079_);
lean_dec(v_b_5064_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5174_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5173_; 
v_a_5083_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5085_ = v___x_5078_;
v_isShared_5086_ = v_isSharedCheck_5173_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5078_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5173_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v_fst_5087_; lean_object* v_snd_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5172_; 
v_fst_5087_ = lean_ctor_get(v_snd_5079_, 0);
v_snd_5088_ = lean_ctor_get(v_snd_5079_, 1);
v_isSharedCheck_5172_ = !lean_is_exclusive(v_snd_5079_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5090_ = v_snd_5079_;
v_isShared_5091_ = v_isSharedCheck_5172_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_snd_5088_);
lean_inc(v_fst_5087_);
lean_dec(v_snd_5079_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5172_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; 
v___x_5092_ = lean_box(0);
if (lean_obj_tag(v_a_5083_) == 0)
{
lean_object* v_seq_5093_; lean_object* v_mvarId_5094_; lean_object* v___x_5095_; 
lean_del_object(v___x_5085_);
v_seq_5093_ = lean_ctor_get(v_a_5083_, 0);
v_mvarId_5094_ = lean_ctor_get(v_head_5076_, 1);
lean_inc(v_mvarId_5094_);
lean_dec(v_head_5076_);
lean_inc(v___y_5073_);
lean_inc_ref(v___y_5072_);
lean_inc(v___y_5071_);
lean_inc_ref(v___y_5070_);
v___x_5095_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5094_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v_a_5096_; 
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_a_5096_);
lean_dec_ref(v___x_5095_);
if (lean_obj_tag(v_a_5096_) == 1)
{
lean_object* v_val_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_tail_5077_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v_kp_5060_);
v_val_5097_ = lean_ctor_get(v_a_5096_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v_a_5096_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5099_ = v_a_5096_;
v_isShared_5100_ = v_isSharedCheck_5128_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_val_5097_);
lean_dec(v_a_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5128_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v_mvarId_5101_; lean_object* v___x_5102_; 
v_mvarId_5101_ = lean_ctor_get(v_snd_5061_, 1);
lean_inc(v_mvarId_5101_);
lean_dec_ref(v_snd_5061_);
v___x_5102_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5101_, v_val_5097_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5118_; 
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5118_ == 0)
{
lean_object* v_unused_5119_; 
v_unused_5119_ = lean_ctor_get(v___x_5102_, 0);
lean_dec(v_unused_5119_);
v___x_5104_ = v___x_5102_;
v_isShared_5105_ = v_isSharedCheck_5118_;
goto v_resetjp_5103_;
}
else
{
lean_dec(v___x_5102_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5118_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v_a_5083_);
v___x_5107_ = v___x_5099_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5083_);
v___x_5107_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5109_; 
if (v_isShared_5091_ == 0)
{
v___x_5109_ = v___x_5090_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_fst_5087_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v_snd_5088_);
v___x_5109_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5111_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5109_);
lean_ctor_set(v___x_5081_, 0, v___x_5107_);
v___x_5111_ = v___x_5081_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5107_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5109_);
v___x_5111_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
lean_object* v___x_5113_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v___x_5111_);
v___x_5113_ = v___x_5104_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v___x_5111_);
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
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_del_object(v___x_5099_);
lean_dec_ref(v_a_5083_);
lean_del_object(v___x_5090_);
lean_dec(v_snd_5088_);
lean_dec(v_fst_5087_);
lean_del_object(v___x_5081_);
v_a_5120_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5102_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5102_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
}
}
else
{
uint8_t v___x_5129_; 
lean_inc(v_seq_5093_);
lean_dec(v_a_5096_);
lean_dec_ref(v_a_5083_);
v___x_5129_ = l_List_isEmpty___redArg(v_seq_5093_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; lean_object* v___x_5132_; 
v___x_5130_ = lean_array_push(v_fst_5087_, v_seq_5093_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v___x_5130_);
v___x_5132_ = v___x_5090_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5130_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_snd_5088_);
v___x_5132_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
lean_object* v___x_5134_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5132_);
lean_ctor_set(v___x_5081_, 0, v___x_5092_);
v___x_5134_ = v___x_5081_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5136_, 1, v___x_5132_);
v___x_5134_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
v_as_x27_5063_ = v_tail_5077_;
v_b_5064_ = v___x_5134_;
goto _start;
}
}
}
else
{
lean_object* v___x_5139_; 
lean_dec(v_seq_5093_);
if (v_isShared_5091_ == 0)
{
v___x_5139_ = v___x_5090_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_fst_5087_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_snd_5088_);
v___x_5139_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5141_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5139_);
lean_ctor_set(v___x_5081_, 0, v___x_5092_);
v___x_5141_ = v___x_5081_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5143_, 1, v___x_5139_);
v___x_5141_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
v_as_x27_5063_ = v_tail_5077_;
v_b_5064_ = v___x_5141_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec_ref(v_a_5083_);
lean_del_object(v___x_5090_);
lean_dec(v_snd_5088_);
lean_dec(v_fst_5087_);
lean_del_object(v___x_5081_);
lean_dec(v_tail_5077_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v_snd_5061_);
lean_dec_ref(v_kp_5060_);
v_a_5145_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5095_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5095_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
else
{
lean_dec(v_head_5076_);
if (v_stopAtFirstFailure_5062_ == 0)
{
lean_object* v_gs_5153_; lean_object* v___x_5154_; lean_object* v___x_5156_; 
lean_del_object(v___x_5085_);
v_gs_5153_ = lean_ctor_get(v_a_5083_, 0);
lean_inc(v_gs_5153_);
lean_dec_ref(v_a_5083_);
v___x_5154_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5088_, v_gs_5153_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 1, v___x_5154_);
v___x_5156_ = v___x_5090_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_fst_5087_);
lean_ctor_set(v_reuseFailAlloc_5161_, 1, v___x_5154_);
v___x_5156_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
lean_object* v___x_5158_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5156_);
lean_ctor_set(v___x_5081_, 0, v___x_5092_);
v___x_5158_ = v___x_5081_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5160_, 1, v___x_5156_);
v___x_5158_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
v_as_x27_5063_ = v_tail_5077_;
v_b_5064_ = v___x_5158_;
goto _start;
}
}
}
else
{
lean_object* v___x_5162_; lean_object* v___x_5164_; 
lean_dec(v_tail_5077_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v_snd_5061_);
lean_dec_ref(v_kp_5060_);
v___x_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5162_, 0, v_a_5083_);
if (v_isShared_5091_ == 0)
{
v___x_5164_ = v___x_5090_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_fst_5087_);
lean_ctor_set(v_reuseFailAlloc_5171_, 1, v_snd_5088_);
v___x_5164_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
lean_object* v___x_5166_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5164_);
lean_ctor_set(v___x_5081_, 0, v___x_5162_);
v___x_5166_ = v___x_5081_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5170_, 1, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5168_; 
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 0, v___x_5166_);
v___x_5168_ = v___x_5085_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
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
}
}
}
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
lean_dec(v_tail_5077_);
lean_dec(v_head_5076_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_snd_5061_);
lean_dec_ref(v_kp_5060_);
v_a_5176_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5078_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5078_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5184_, lean_object* v_snd_5185_, lean_object* v_stopAtFirstFailure_5186_, lean_object* v_as_x27_5187_, lean_object* v_b_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5199_; lean_object* v_res_5200_; 
v_stopAtFirstFailure_boxed_5199_ = lean_unbox(v_stopAtFirstFailure_5186_);
v_res_5200_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5184_, v_snd_5185_, v_stopAtFirstFailure_boxed_5199_, v_as_x27_5187_, v_b_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5201_, lean_object* v_c_5202_, lean_object* v___x_5203_, lean_object* v___x_5204_, uint8_t v_isRec_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
if (lean_obj_tag(v_a_5206_) == 0)
{
lean_object* v___x_5208_; 
lean_dec(v___x_5204_);
lean_dec_ref(v___x_5203_);
lean_dec_ref(v_snd_5201_);
v___x_5208_ = lean_array_to_list(v_a_5207_);
return v___x_5208_;
}
else
{
lean_object* v_toGoalState_5209_; lean_object* v_split_5210_; lean_object* v_head_5211_; lean_object* v_tail_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5274_; 
v_toGoalState_5209_ = lean_ctor_get(v_snd_5201_, 0);
lean_inc_ref(v_toGoalState_5209_);
v_split_5210_ = lean_ctor_get(v_toGoalState_5209_, 15);
lean_inc_ref(v_split_5210_);
v_head_5211_ = lean_ctor_get(v_a_5206_, 0);
v_tail_5212_ = lean_ctor_get(v_a_5206_, 1);
v_isSharedCheck_5274_ = !lean_is_exclusive(v_a_5206_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5214_ = v_a_5206_;
v_isShared_5215_ = v_isSharedCheck_5274_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_tail_5212_);
lean_inc(v_head_5211_);
lean_dec(v_a_5206_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5274_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v_nextDeclIdx_5216_; lean_object* v_canon_5217_; lean_object* v_enodeMap_5218_; lean_object* v_exprs_5219_; lean_object* v_parents_5220_; lean_object* v_congrTable_5221_; lean_object* v_appMap_5222_; lean_object* v_indicesFound_5223_; lean_object* v_newFacts_5224_; uint8_t v_inconsistent_5225_; lean_object* v_nextIdx_5226_; lean_object* v_newRawFacts_5227_; lean_object* v_facts_5228_; lean_object* v_extThms_5229_; lean_object* v_ematch_5230_; lean_object* v_inj_5231_; lean_object* v_clean_5232_; lean_object* v_sstates_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5272_; 
v_nextDeclIdx_5216_ = lean_ctor_get(v_toGoalState_5209_, 0);
v_canon_5217_ = lean_ctor_get(v_toGoalState_5209_, 1);
v_enodeMap_5218_ = lean_ctor_get(v_toGoalState_5209_, 2);
v_exprs_5219_ = lean_ctor_get(v_toGoalState_5209_, 3);
v_parents_5220_ = lean_ctor_get(v_toGoalState_5209_, 4);
v_congrTable_5221_ = lean_ctor_get(v_toGoalState_5209_, 5);
v_appMap_5222_ = lean_ctor_get(v_toGoalState_5209_, 6);
v_indicesFound_5223_ = lean_ctor_get(v_toGoalState_5209_, 7);
v_newFacts_5224_ = lean_ctor_get(v_toGoalState_5209_, 8);
v_inconsistent_5225_ = lean_ctor_get_uint8(v_toGoalState_5209_, sizeof(void*)*18);
v_nextIdx_5226_ = lean_ctor_get(v_toGoalState_5209_, 9);
v_newRawFacts_5227_ = lean_ctor_get(v_toGoalState_5209_, 10);
v_facts_5228_ = lean_ctor_get(v_toGoalState_5209_, 11);
v_extThms_5229_ = lean_ctor_get(v_toGoalState_5209_, 12);
v_ematch_5230_ = lean_ctor_get(v_toGoalState_5209_, 13);
v_inj_5231_ = lean_ctor_get(v_toGoalState_5209_, 14);
v_clean_5232_ = lean_ctor_get(v_toGoalState_5209_, 16);
v_sstates_5233_ = lean_ctor_get(v_toGoalState_5209_, 17);
v_isSharedCheck_5272_ = !lean_is_exclusive(v_toGoalState_5209_);
if (v_isSharedCheck_5272_ == 0)
{
lean_object* v_unused_5273_; 
v_unused_5273_ = lean_ctor_get(v_toGoalState_5209_, 15);
lean_dec(v_unused_5273_);
v___x_5235_ = v_toGoalState_5209_;
v_isShared_5236_ = v_isSharedCheck_5272_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_sstates_5233_);
lean_inc(v_clean_5232_);
lean_inc(v_inj_5231_);
lean_inc(v_ematch_5230_);
lean_inc(v_extThms_5229_);
lean_inc(v_facts_5228_);
lean_inc(v_newRawFacts_5227_);
lean_inc(v_nextIdx_5226_);
lean_inc(v_newFacts_5224_);
lean_inc(v_indicesFound_5223_);
lean_inc(v_appMap_5222_);
lean_inc(v_congrTable_5221_);
lean_inc(v_parents_5220_);
lean_inc(v_exprs_5219_);
lean_inc(v_enodeMap_5218_);
lean_inc(v_canon_5217_);
lean_inc(v_nextDeclIdx_5216_);
lean_dec(v_toGoalState_5209_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5272_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v_num_5237_; lean_object* v_candidates_5238_; lean_object* v_added_5239_; lean_object* v_resolved_5240_; lean_object* v_trace_5241_; lean_object* v_lookaheads_5242_; lean_object* v_argPosMap_5243_; lean_object* v_argsAt_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5271_; 
v_num_5237_ = lean_ctor_get(v_split_5210_, 0);
v_candidates_5238_ = lean_ctor_get(v_split_5210_, 1);
v_added_5239_ = lean_ctor_get(v_split_5210_, 2);
v_resolved_5240_ = lean_ctor_get(v_split_5210_, 3);
v_trace_5241_ = lean_ctor_get(v_split_5210_, 4);
v_lookaheads_5242_ = lean_ctor_get(v_split_5210_, 5);
v_argPosMap_5243_ = lean_ctor_get(v_split_5210_, 6);
v_argsAt_5244_ = lean_ctor_get(v_split_5210_, 7);
v_isSharedCheck_5271_ = !lean_is_exclusive(v_split_5210_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5246_ = v_split_5210_;
v_isShared_5247_ = v_isSharedCheck_5271_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_argsAt_5244_);
lean_inc(v_argPosMap_5243_);
lean_inc(v_lookaheads_5242_);
lean_inc(v_trace_5241_);
lean_inc(v_resolved_5240_);
lean_inc(v_added_5239_);
lean_inc(v_candidates_5238_);
lean_inc(v_num_5237_);
lean_dec(v_split_5210_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5271_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5248_; lean_object* v___y_5250_; uint8_t v___y_5266_; lean_object* v___x_5269_; uint8_t v___x_5270_; 
v___x_5248_ = lean_array_get_size(v_a_5207_);
v___x_5269_ = lean_unsigned_to_nat(0u);
v___x_5270_ = lean_nat_dec_lt(v___x_5269_, v___x_5248_);
if (v___x_5270_ == 0)
{
v___y_5266_ = v_isRec_5205_;
goto v___jp_5265_;
}
else
{
v___y_5266_ = v___x_5270_;
goto v___jp_5265_;
}
v___jp_5249_:
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5254_; 
v___x_5251_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5202_);
lean_inc(v___x_5204_);
lean_inc_ref(v___x_5203_);
v___x_5252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5203_);
lean_ctor_set(v___x_5252_, 1, v___x_5248_);
lean_ctor_set(v___x_5252_, 2, v___x_5204_);
lean_ctor_set(v___x_5252_, 3, v___x_5251_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 1, v_trace_5241_);
lean_ctor_set(v___x_5214_, 0, v___x_5252_);
v___x_5254_ = v___x_5214_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5252_);
lean_ctor_set(v_reuseFailAlloc_5264_, 1, v_trace_5241_);
v___x_5254_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
lean_object* v___x_5256_; 
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 4, v___x_5254_);
lean_ctor_set(v___x_5246_, 0, v___y_5250_);
v___x_5256_ = v___x_5246_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___y_5250_);
lean_ctor_set(v_reuseFailAlloc_5263_, 1, v_candidates_5238_);
lean_ctor_set(v_reuseFailAlloc_5263_, 2, v_added_5239_);
lean_ctor_set(v_reuseFailAlloc_5263_, 3, v_resolved_5240_);
lean_ctor_set(v_reuseFailAlloc_5263_, 4, v___x_5254_);
lean_ctor_set(v_reuseFailAlloc_5263_, 5, v_lookaheads_5242_);
lean_ctor_set(v_reuseFailAlloc_5263_, 6, v_argPosMap_5243_);
lean_ctor_set(v_reuseFailAlloc_5263_, 7, v_argsAt_5244_);
v___x_5256_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
lean_object* v___x_5258_; 
if (v_isShared_5236_ == 0)
{
lean_ctor_set(v___x_5235_, 15, v___x_5256_);
v___x_5258_ = v___x_5235_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_nextDeclIdx_5216_);
lean_ctor_set(v_reuseFailAlloc_5262_, 1, v_canon_5217_);
lean_ctor_set(v_reuseFailAlloc_5262_, 2, v_enodeMap_5218_);
lean_ctor_set(v_reuseFailAlloc_5262_, 3, v_exprs_5219_);
lean_ctor_set(v_reuseFailAlloc_5262_, 4, v_parents_5220_);
lean_ctor_set(v_reuseFailAlloc_5262_, 5, v_congrTable_5221_);
lean_ctor_set(v_reuseFailAlloc_5262_, 6, v_appMap_5222_);
lean_ctor_set(v_reuseFailAlloc_5262_, 7, v_indicesFound_5223_);
lean_ctor_set(v_reuseFailAlloc_5262_, 8, v_newFacts_5224_);
lean_ctor_set(v_reuseFailAlloc_5262_, 9, v_nextIdx_5226_);
lean_ctor_set(v_reuseFailAlloc_5262_, 10, v_newRawFacts_5227_);
lean_ctor_set(v_reuseFailAlloc_5262_, 11, v_facts_5228_);
lean_ctor_set(v_reuseFailAlloc_5262_, 12, v_extThms_5229_);
lean_ctor_set(v_reuseFailAlloc_5262_, 13, v_ematch_5230_);
lean_ctor_set(v_reuseFailAlloc_5262_, 14, v_inj_5231_);
lean_ctor_set(v_reuseFailAlloc_5262_, 15, v___x_5256_);
lean_ctor_set(v_reuseFailAlloc_5262_, 16, v_clean_5232_);
lean_ctor_set(v_reuseFailAlloc_5262_, 17, v_sstates_5233_);
lean_ctor_set_uint8(v_reuseFailAlloc_5262_, sizeof(void*)*18, v_inconsistent_5225_);
v___x_5258_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5259_, 0, v___x_5258_);
lean_ctor_set(v___x_5259_, 1, v_head_5211_);
v___x_5260_ = lean_array_push(v_a_5207_, v___x_5259_);
v_a_5206_ = v_tail_5212_;
v_a_5207_ = v___x_5260_;
goto _start;
}
}
}
}
v___jp_5265_:
{
if (v___y_5266_ == 0)
{
v___y_5250_ = v_num_5237_;
goto v___jp_5249_;
}
else
{
lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5267_ = lean_unsigned_to_nat(1u);
v___x_5268_ = lean_nat_add(v_num_5237_, v___x_5267_);
lean_dec(v_num_5237_);
v___y_5250_ = v___x_5268_;
goto v___jp_5249_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5275_, lean_object* v_c_5276_, lean_object* v___x_5277_, lean_object* v___x_5278_, lean_object* v_isRec_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_){
_start:
{
uint8_t v_isRec_boxed_5282_; lean_object* v_res_5283_; 
v_isRec_boxed_5282_ = lean_unbox(v_isRec_5279_);
v_res_5283_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5275_, v_c_5276_, v___x_5277_, v___x_5278_, v_isRec_boxed_5282_, v_a_5280_, v_a_5281_);
lean_dec_ref(v_c_5276_);
return v_res_5283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5286_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5287_, 0, v___x_5286_);
lean_ctor_set(v___x_5287_, 1, v___x_5286_);
return v___x_5287_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2(void){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5288_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1);
v___x_5289_ = lean_box(0);
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
lean_ctor_set(v___x_5290_, 1, v___x_5288_);
return v___x_5290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9(void){
_start:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5309_ = lean_box(0);
v___x_5310_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__8));
v___x_5311_ = l_Lean_mkConst(v___x_5310_, v___x_5309_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5312_, lean_object* v_numCases_5313_, uint8_t v_isRec_5314_, uint8_t v_stopAtFirstFailure_5315_, uint8_t v_compress_5316_, lean_object* v_goal_5317_, lean_object* v_kp_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v___x_5329_; 
v___x_5329_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5320_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5331_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5330_);
lean_dec_ref(v___x_5329_);
lean_inc(v_a_5327_);
lean_inc_ref(v_a_5326_);
lean_inc(v_a_5325_);
lean_inc_ref(v_a_5324_);
lean_inc_ref(v_goal_5317_);
v___x_5331_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5317_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v_a_5332_; uint8_t v_trace_5333_; lean_object* v_mvarId_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___f_5338_; lean_object* v___x_5339_; 
v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
lean_inc(v_a_5332_);
lean_dec_ref(v___x_5331_);
v_trace_5333_ = lean_ctor_get_uint8(v_a_5330_, sizeof(void*)*11);
lean_dec(v_a_5330_);
v_mvarId_5334_ = lean_ctor_get(v_goal_5317_, 1);
lean_inc(v_mvarId_5334_);
v___x_5335_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5312_);
v___x_5336_ = lean_box(v_trace_5333_);
v___x_5337_ = lean_box(v_isRec_5314_);
lean_inc(v_a_5332_);
lean_inc_ref(v_c_5312_);
lean_inc_ref(v___x_5335_);
v___f_5338_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 17, 7);
lean_closure_set(v___f_5338_, 0, v_goal_5317_);
lean_closure_set(v___f_5338_, 1, v___x_5335_);
lean_closure_set(v___f_5338_, 2, v___x_5336_);
lean_closure_set(v___f_5338_, 3, v_c_5312_);
lean_closure_set(v___f_5338_, 4, v_a_5332_);
lean_closure_set(v___f_5338_, 5, v_numCases_5313_);
lean_closure_set(v___f_5338_, 6, v___x_5337_);
lean_inc(v_a_5327_);
lean_inc_ref(v_a_5326_);
lean_inc(v_a_5325_);
lean_inc_ref(v_a_5324_);
lean_inc(v_a_5323_);
lean_inc_ref(v_a_5322_);
lean_inc(v_a_5321_);
lean_inc_ref(v_a_5320_);
lean_inc(v_a_5319_);
v___x_5339_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5334_, v___f_5338_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_a_5340_; lean_object* v_fst_5341_; lean_object* v_snd_5342_; lean_object* v_fst_5343_; lean_object* v_snd_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; 
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_a_5340_);
lean_dec_ref(v___x_5339_);
v_fst_5341_ = lean_ctor_get(v_a_5340_, 0);
lean_inc(v_fst_5341_);
v_snd_5342_ = lean_ctor_get(v_a_5340_, 1);
lean_inc(v_snd_5342_);
lean_dec(v_a_5340_);
v_fst_5343_ = lean_ctor_get(v_fst_5341_, 0);
lean_inc(v_fst_5343_);
v_snd_5344_ = lean_ctor_get(v_fst_5341_, 1);
lean_inc(v_snd_5344_);
lean_dec(v_fst_5341_);
v___x_5345_ = l_List_lengthTR___redArg(v_fst_5343_);
v___x_5346_ = lean_unsigned_to_nat(0u);
v___x_5347_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
lean_inc_ref(v___x_5335_);
lean_inc(v_snd_5342_);
v___x_5348_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5342_, v_c_5312_, v___x_5335_, v___x_5345_, v_isRec_5314_, v_fst_5343_, v___x_5347_);
lean_dec_ref(v_c_5312_);
v___x_5349_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2);
lean_inc(v_a_5327_);
lean_inc_ref(v_a_5326_);
lean_inc(v_a_5325_);
lean_inc_ref(v_a_5324_);
lean_inc(v_a_5323_);
lean_inc_ref(v_a_5322_);
lean_inc(v_a_5321_);
lean_inc_ref(v_a_5320_);
lean_inc(v_a_5319_);
lean_inc(v_snd_5342_);
v___x_5350_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5318_, v_snd_5342_, v_stopAtFirstFailure_5315_, v___x_5348_, v___x_5349_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
if (lean_obj_tag(v___x_5350_) == 0)
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5465_; 
v_a_5351_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5353_ = v___x_5350_;
v_isShared_5354_ = v_isSharedCheck_5465_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5350_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5465_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v_fst_5355_; 
v_fst_5355_ = lean_ctor_get(v_a_5351_, 0);
if (lean_obj_tag(v_fst_5355_) == 0)
{
lean_object* v_snd_5356_; lean_object* v_mvarId_5357_; lean_object* v___x_5358_; 
lean_del_object(v___x_5353_);
v_snd_5356_ = lean_ctor_get(v_a_5351_, 1);
lean_inc(v_snd_5356_);
lean_dec(v_a_5351_);
v_mvarId_5357_ = lean_ctor_get(v_snd_5342_, 1);
lean_inc(v_mvarId_5357_);
lean_dec(v_snd_5342_);
lean_inc(v_mvarId_5357_);
v___x_5358_ = l_Lean_MVarId_getType(v_mvarId_5357_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5452_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5361_ = v___x_5358_;
v_isShared_5362_ = v_isSharedCheck_5452_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5358_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5452_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v_fst_5363_; lean_object* v_snd_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5451_; 
v_fst_5363_ = lean_ctor_get(v_snd_5356_, 0);
v_snd_5364_ = lean_ctor_get(v_snd_5356_, 1);
v_isSharedCheck_5451_ = !lean_is_exclusive(v_snd_5356_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5366_ = v_snd_5356_;
v_isShared_5367_ = v_isSharedCheck_5451_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_snd_5364_);
lean_inc(v_fst_5363_);
lean_dec(v_snd_5356_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5451_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___y_5369_; lean_object* v___y_5370_; lean_object* v___y_5371_; lean_object* v___y_5372_; lean_object* v___y_5373_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v___y_5377_; uint8_t v___x_5440_; 
v___x_5440_ = l_Lean_Expr_isFalse(v_a_5359_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v_a_5443_; lean_object* v___x_5444_; 
v___x_5441_ = l_Lean_mkMVar(v_a_5332_);
v___x_5442_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5441_, v_a_5325_);
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref(v___x_5442_);
lean_inc(v_mvarId_5357_);
v___x_5444_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5357_, v_a_5443_, v_a_5325_);
lean_dec_ref(v___x_5444_);
v___y_5369_ = v_a_5319_;
v___y_5370_ = v_a_5320_;
v___y_5371_ = v_a_5321_;
v___y_5372_ = v_a_5322_;
v___y_5373_ = v_a_5323_;
v___y_5374_ = v_a_5324_;
v___y_5375_ = v_a_5325_;
v___y_5376_ = v_a_5326_;
v___y_5377_ = v_a_5327_;
goto v___jp_5368_;
}
else
{
lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v_a_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5445_ = l_Lean_mkMVar(v_a_5332_);
v___x_5446_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5445_, v_a_5325_);
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
lean_inc(v_a_5447_);
lean_dec_ref(v___x_5446_);
v___x_5448_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9);
v___x_5449_ = l_Lean_Meta_mkExpectedPropHint(v_a_5447_, v___x_5448_);
lean_inc(v_mvarId_5357_);
v___x_5450_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5357_, v___x_5449_, v_a_5325_);
lean_dec_ref(v___x_5450_);
v___y_5369_ = v_a_5319_;
v___y_5370_ = v_a_5320_;
v___y_5371_ = v_a_5321_;
v___y_5372_ = v_a_5322_;
v___y_5373_ = v_a_5323_;
v___y_5374_ = v_a_5324_;
v___y_5375_ = v_a_5325_;
v___y_5376_ = v_a_5326_;
v___y_5377_ = v_a_5327_;
goto v___jp_5368_;
}
v___jp_5368_:
{
lean_object* v___x_5378_; uint8_t v___x_5379_; 
v___x_5378_ = lean_array_get_size(v_snd_5364_);
v___x_5379_ = lean_nat_dec_eq(v___x_5378_, v___x_5346_);
if (v___x_5379_ == 0)
{
lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5383_; 
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_del_object(v___x_5366_);
lean_dec(v_fst_5363_);
lean_dec(v_mvarId_5357_);
lean_dec(v_snd_5344_);
lean_dec_ref(v___x_5335_);
v___x_5380_ = lean_array_to_list(v_snd_5364_);
v___x_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5380_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v___x_5381_);
v___x_5383_ = v___x_5361_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v___x_5381_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
else
{
lean_dec(v_snd_5364_);
if (v_trace_5333_ == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5387_; 
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_del_object(v___x_5366_);
lean_dec(v_fst_5363_);
lean_dec(v_mvarId_5357_);
lean_dec(v_snd_5344_);
lean_dec_ref(v___x_5335_);
v___x_5385_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v___x_5385_);
v___x_5387_ = v___x_5361_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5385_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_del_object(v___x_5361_);
v___x_5389_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_5389_, 0, v___x_5335_);
lean_inc(v___y_5377_);
lean_inc_ref(v___y_5376_);
v___x_5390_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5357_, v___x_5389_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; uint64_t v___x_5392_; lean_object* v___x_5393_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
lean_inc(v_a_5391_);
lean_dec_ref(v___x_5390_);
v___x_5392_ = lean_unbox_uint64(v_a_5391_);
lean_dec(v_a_5391_);
v___x_5393_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_snd_5344_, v___x_5392_, v___y_5376_);
lean_dec(v_snd_5344_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v_ref_5395_; uint8_t v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5401_; 
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref(v___x_5393_);
v_ref_5395_ = lean_ctor_get(v___y_5376_, 5);
v___x_5396_ = 0;
v___x_5397_ = l_Lean_SourceInfo_fromRef(v_ref_5395_, v___x_5396_);
v___x_5398_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5399_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5));
lean_inc(v___x_5397_);
if (v_isShared_5367_ == 0)
{
lean_ctor_set_tag(v___x_5366_, 2);
lean_ctor_set(v___x_5366_, 1, v___x_5398_);
lean_ctor_set(v___x_5366_, 0, v___x_5397_);
v___x_5401_ = v___x_5366_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5397_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5398_);
v___x_5401_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5402_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7));
lean_inc(v___x_5397_);
v___x_5403_ = l_Lean_Syntax_node1(v___x_5397_, v___x_5402_, v_a_5394_);
v___x_5404_ = l_Lean_Syntax_node2(v___x_5397_, v___x_5399_, v___x_5401_, v___x_5403_);
v___x_5405_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v___x_5404_, v_fst_5363_, v_compress_5316_, v___y_5376_, v___y_5377_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5414_; 
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5408_ = v___x_5405_;
v_isShared_5409_ = v_isSharedCheck_5414_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5405_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5414_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5410_; lean_object* v___x_5412_; 
v___x_5410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5410_, 0, v_a_5406_);
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 0, v___x_5410_);
v___x_5412_ = v___x_5408_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5410_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
v_a_5415_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5405_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5405_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_del_object(v___x_5366_);
lean_dec(v_fst_5363_);
v_a_5424_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5393_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5393_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_del_object(v___x_5366_);
lean_dec(v_fst_5363_);
lean_dec(v_snd_5344_);
v_a_5432_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5390_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5390_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
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
lean_object* v_a_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5460_; 
lean_dec(v_mvarId_5357_);
lean_dec(v_snd_5356_);
lean_dec(v_snd_5344_);
lean_dec_ref(v___x_5335_);
lean_dec(v_a_5332_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
v_a_5453_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5460_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5460_ == 0)
{
v___x_5455_ = v___x_5358_;
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_a_5453_);
lean_dec(v___x_5358_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v___x_5458_; 
if (v_isShared_5456_ == 0)
{
v___x_5458_ = v___x_5455_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
else
{
lean_object* v_val_5461_; lean_object* v___x_5463_; 
lean_inc_ref(v_fst_5355_);
lean_dec(v_a_5351_);
lean_dec(v_snd_5344_);
lean_dec(v_snd_5342_);
lean_dec_ref(v___x_5335_);
lean_dec(v_a_5332_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
v_val_5461_ = lean_ctor_get(v_fst_5355_, 0);
lean_inc(v_val_5461_);
lean_dec_ref(v_fst_5355_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 0, v_val_5461_);
v___x_5463_ = v___x_5353_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_val_5461_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
}
else
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
lean_dec(v_snd_5344_);
lean_dec(v_snd_5342_);
lean_dec_ref(v___x_5335_);
lean_dec(v_a_5332_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
v_a_5466_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5350_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5350_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5471_; 
if (v_isShared_5469_ == 0)
{
v___x_5471_ = v___x_5468_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
else
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
lean_dec_ref(v___x_5335_);
lean_dec(v_a_5332_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_kp_5318_);
lean_dec_ref(v_c_5312_);
v_a_5474_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5339_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5339_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec(v_a_5330_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_kp_5318_);
lean_dec_ref(v_goal_5317_);
lean_dec(v_numCases_5313_);
lean_dec_ref(v_c_5312_);
v_a_5482_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5331_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5331_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
else
{
lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5497_; 
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_kp_5318_);
lean_dec_ref(v_goal_5317_);
lean_dec(v_numCases_5313_);
lean_dec_ref(v_c_5312_);
v_a_5490_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5492_ = v___x_5329_;
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_dec(v___x_5329_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5495_; 
if (v_isShared_5493_ == 0)
{
v___x_5495_ = v___x_5492_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5490_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5498_ = _args[0];
lean_object* v_numCases_5499_ = _args[1];
lean_object* v_isRec_5500_ = _args[2];
lean_object* v_stopAtFirstFailure_5501_ = _args[3];
lean_object* v_compress_5502_ = _args[4];
lean_object* v_goal_5503_ = _args[5];
lean_object* v_kp_5504_ = _args[6];
lean_object* v_a_5505_ = _args[7];
lean_object* v_a_5506_ = _args[8];
lean_object* v_a_5507_ = _args[9];
lean_object* v_a_5508_ = _args[10];
lean_object* v_a_5509_ = _args[11];
lean_object* v_a_5510_ = _args[12];
lean_object* v_a_5511_ = _args[13];
lean_object* v_a_5512_ = _args[14];
lean_object* v_a_5513_ = _args[15];
lean_object* v_a_5514_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5515_; uint8_t v_stopAtFirstFailure_boxed_5516_; uint8_t v_compress_boxed_5517_; lean_object* v_res_5518_; 
v_isRec_boxed_5515_ = lean_unbox(v_isRec_5500_);
v_stopAtFirstFailure_boxed_5516_ = lean_unbox(v_stopAtFirstFailure_5501_);
v_compress_boxed_5517_ = lean_unbox(v_compress_5502_);
v_res_5518_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5498_, v_numCases_5499_, v_isRec_boxed_5515_, v_stopAtFirstFailure_boxed_5516_, v_compress_boxed_5517_, v_goal_5503_, v_kp_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5519_, lean_object* v_numCases_5520_, uint8_t v_isRec_5521_, uint8_t v_stopAtFirstFailure_5522_, uint8_t v_compress_5523_, lean_object* v_goal_5524_, lean_object* v_x_5525_, lean_object* v_kp_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___x_5537_; 
v___x_5537_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5519_, v_numCases_5520_, v_isRec_5521_, v_stopAtFirstFailure_5522_, v_compress_5523_, v_goal_5524_, v_kp_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
return v___x_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5538_ = _args[0];
lean_object* v_numCases_5539_ = _args[1];
lean_object* v_isRec_5540_ = _args[2];
lean_object* v_stopAtFirstFailure_5541_ = _args[3];
lean_object* v_compress_5542_ = _args[4];
lean_object* v_goal_5543_ = _args[5];
lean_object* v_x_5544_ = _args[6];
lean_object* v_kp_5545_ = _args[7];
lean_object* v_a_5546_ = _args[8];
lean_object* v_a_5547_ = _args[9];
lean_object* v_a_5548_ = _args[10];
lean_object* v_a_5549_ = _args[11];
lean_object* v_a_5550_ = _args[12];
lean_object* v_a_5551_ = _args[13];
lean_object* v_a_5552_ = _args[14];
lean_object* v_a_5553_ = _args[15];
lean_object* v_a_5554_ = _args[16];
lean_object* v_a_5555_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5556_; uint8_t v_stopAtFirstFailure_boxed_5557_; uint8_t v_compress_boxed_5558_; lean_object* v_res_5559_; 
v_isRec_boxed_5556_ = lean_unbox(v_isRec_5540_);
v_stopAtFirstFailure_boxed_5557_ = lean_unbox(v_stopAtFirstFailure_5541_);
v_compress_boxed_5558_ = lean_unbox(v_compress_5542_);
v_res_5559_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5538_, v_numCases_5539_, v_isRec_boxed_5556_, v_stopAtFirstFailure_boxed_5557_, v_compress_boxed_5558_, v_goal_5543_, v_x_5544_, v_kp_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_);
lean_dec_ref(v_x_5544_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5560_, lean_object* v_snd_5561_, uint8_t v_stopAtFirstFailure_5562_, lean_object* v_as_5563_, lean_object* v_as_x27_5564_, lean_object* v_b_5565_, lean_object* v_a_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
lean_object* v___x_5577_; 
v___x_5577_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5560_, v_snd_5561_, v_stopAtFirstFailure_5562_, v_as_x27_5564_, v_b_5565_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
return v___x_5577_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5578_ = _args[0];
lean_object* v_snd_5579_ = _args[1];
lean_object* v_stopAtFirstFailure_5580_ = _args[2];
lean_object* v_as_5581_ = _args[3];
lean_object* v_as_x27_5582_ = _args[4];
lean_object* v_b_5583_ = _args[5];
lean_object* v_a_5584_ = _args[6];
lean_object* v___y_5585_ = _args[7];
lean_object* v___y_5586_ = _args[8];
lean_object* v___y_5587_ = _args[9];
lean_object* v___y_5588_ = _args[10];
lean_object* v___y_5589_ = _args[11];
lean_object* v___y_5590_ = _args[12];
lean_object* v___y_5591_ = _args[13];
lean_object* v___y_5592_ = _args[14];
lean_object* v___y_5593_ = _args[15];
lean_object* v___y_5594_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5595_; lean_object* v_res_5596_; 
v_stopAtFirstFailure_boxed_5595_ = lean_unbox(v_stopAtFirstFailure_5580_);
v_res_5596_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5578_, v_snd_5579_, v_stopAtFirstFailure_boxed_5595_, v_as_5581_, v_as_x27_5582_, v_b_5583_, v_a_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
lean_dec(v_as_5581_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_5597_, lean_object* v_val_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5597_, v_val_5598_, v___y_5605_);
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_5610_, lean_object* v_val_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_5610_, v_val_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
lean_dec(v___y_5612_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_5623_, lean_object* v_x_5624_, lean_object* v_x_5625_, lean_object* v_x_5626_){
_start:
{
lean_object* v___x_5627_; 
v___x_5627_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_5624_, v_x_5625_, v_x_5626_);
return v___x_5627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_5628_, lean_object* v_x_5629_, size_t v_x_5630_, size_t v_x_5631_, lean_object* v_x_5632_, lean_object* v_x_5633_){
_start:
{
lean_object* v___x_5634_; 
v___x_5634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5629_, v_x_5630_, v_x_5631_, v_x_5632_, v_x_5633_);
return v___x_5634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_5635_, lean_object* v_x_5636_, lean_object* v_x_5637_, lean_object* v_x_5638_, lean_object* v_x_5639_, lean_object* v_x_5640_){
_start:
{
size_t v_x_88610__boxed_5641_; size_t v_x_88611__boxed_5642_; lean_object* v_res_5643_; 
v_x_88610__boxed_5641_ = lean_unbox_usize(v_x_5637_);
lean_dec(v_x_5637_);
v_x_88611__boxed_5642_ = lean_unbox_usize(v_x_5638_);
lean_dec(v_x_5638_);
v_res_5643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_5635_, v_x_5636_, v_x_88610__boxed_5641_, v_x_88611__boxed_5642_, v_x_5639_, v_x_5640_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_5644_, lean_object* v_n_5645_, lean_object* v_k_5646_, lean_object* v_v_5647_){
_start:
{
lean_object* v___x_5648_; 
v___x_5648_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_5645_, v_k_5646_, v_v_5647_);
return v___x_5648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_5649_, size_t v_depth_5650_, lean_object* v_keys_5651_, lean_object* v_vals_5652_, lean_object* v_heq_5653_, lean_object* v_i_5654_, lean_object* v_entries_5655_){
_start:
{
lean_object* v___x_5656_; 
v___x_5656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_5650_, v_keys_5651_, v_vals_5652_, v_i_5654_, v_entries_5655_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_5657_, lean_object* v_depth_5658_, lean_object* v_keys_5659_, lean_object* v_vals_5660_, lean_object* v_heq_5661_, lean_object* v_i_5662_, lean_object* v_entries_5663_){
_start:
{
size_t v_depth_boxed_5664_; lean_object* v_res_5665_; 
v_depth_boxed_5664_ = lean_unbox_usize(v_depth_5658_);
lean_dec(v_depth_5658_);
v_res_5665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_5657_, v_depth_boxed_5664_, v_keys_5659_, v_vals_5660_, v_heq_5661_, v_i_5662_, v_entries_5663_);
lean_dec_ref(v_vals_5660_);
lean_dec_ref(v_keys_5659_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_5666_, lean_object* v_x_5667_, lean_object* v_x_5668_, lean_object* v_x_5669_, lean_object* v_x_5670_){
_start:
{
lean_object* v___x_5671_; 
v___x_5671_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_5667_, v_x_5668_, v_x_5669_, v_x_5670_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v_goal_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5683_ = lean_st_mk_ref(v_goal_5672_);
lean_inc(v___x_5683_);
v___x_5684_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_5683_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5694_; 
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5687_ = v___x_5684_;
v_isShared_5688_ = v_isSharedCheck_5694_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5684_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5694_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5692_; 
v___x_5689_ = lean_st_ref_get(v___x_5683_);
lean_dec(v___x_5683_);
v___x_5690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5690_, 0, v_a_5685_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 0, v___x_5690_);
v___x_5692_ = v___x_5687_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v___x_5690_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
else
{
lean_object* v_a_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
lean_dec(v___x_5683_);
v_a_5695_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5697_ = v___x_5684_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_a_5695_);
lean_dec(v___x_5684_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v_goal_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_){
_start:
{
lean_object* v_res_5714_; 
v_res_5714_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v_goal_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
lean_object* v___x_5728_; 
v___x_5728_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_5715_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
return v___x_5728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
lean_object* v_res_5742_; 
v_res_5742_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
lean_dec_ref(v___y_5730_);
return v_res_5742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_5743_, lean_object* v___f_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_){
_start:
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_5758_, 0, v___y_5743_);
v___x_5759_ = l_Lean_Meta_Grind_Action_andThen(v___x_5758_, v___f_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_5760_, lean_object* v___f_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_5760_, v___f_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_5777_, uint8_t v_compress_5778_, lean_object* v_goal_5779_, lean_object* v_kna_5780_, lean_object* v_kp_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_){
_start:
{
lean_object* v_mvarId_5792_; lean_object* v___f_5793_; lean_object* v___x_5794_; 
v_mvarId_5792_ = lean_ctor_get(v_goal_5779_, 1);
lean_inc(v_mvarId_5792_);
v___f_5793_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5793_, 0, v_goal_5779_);
lean_inc(v_a_5790_);
lean_inc_ref(v_a_5789_);
lean_inc(v_a_5788_);
lean_inc_ref(v_a_5787_);
lean_inc(v_a_5786_);
lean_inc_ref(v_a_5785_);
lean_inc(v_a_5784_);
lean_inc_ref(v_a_5783_);
lean_inc(v_a_5782_);
v___x_5794_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5792_, v___f_5793_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_);
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_object* v_a_5795_; lean_object* v_fst_5796_; 
v_a_5795_ = lean_ctor_get(v___x_5794_, 0);
lean_inc(v_a_5795_);
lean_dec_ref(v___x_5794_);
v_fst_5796_ = lean_ctor_get(v_a_5795_, 0);
if (lean_obj_tag(v_fst_5796_) == 1)
{
lean_object* v_snd_5797_; lean_object* v_c_5798_; lean_object* v_numCases_5799_; uint8_t v_isRec_5800_; lean_object* v___f_5801_; lean_object* v___y_5803_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; uint8_t v___y_5814_; uint8_t v___x_5816_; 
lean_inc_ref(v_fst_5796_);
v_snd_5797_ = lean_ctor_get(v_a_5795_, 1);
lean_inc(v_snd_5797_);
lean_dec(v_a_5795_);
v_c_5798_ = lean_ctor_get(v_fst_5796_, 0);
lean_inc_ref(v_c_5798_);
v_numCases_5799_ = lean_ctor_get(v_fst_5796_, 1);
lean_inc(v_numCases_5799_);
v_isRec_5800_ = lean_ctor_get_uint8(v_fst_5796_, sizeof(void*)*2);
lean_dec_ref(v_fst_5796_);
v___f_5801_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___x_5810_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5798_);
lean_inc(v_snd_5797_);
v___x_5811_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_5797_, v___x_5810_);
lean_dec_ref(v___x_5810_);
v___x_5812_ = lean_unsigned_to_nat(1u);
v___x_5816_ = lean_nat_dec_lt(v___x_5812_, v_numCases_5799_);
if (v___x_5816_ == 0)
{
v___y_5814_ = v_isRec_5800_;
goto v___jp_5813_;
}
else
{
v___y_5814_ = v___x_5816_;
goto v___jp_5813_;
}
v___jp_5802_:
{
lean_object* v___f_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___f_5804_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_5804_, 0, v___y_5803_);
lean_closure_set(v___f_5804_, 1, v___f_5801_);
v___x_5805_ = lean_box(v_isRec_5800_);
v___x_5806_ = lean_box(v_stopAtFirstFailure_5777_);
v___x_5807_ = lean_box(v_compress_5778_);
v___x_5808_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 18, 5);
lean_closure_set(v___x_5808_, 0, v_c_5798_);
lean_closure_set(v___x_5808_, 1, v_numCases_5799_);
lean_closure_set(v___x_5808_, 2, v___x_5805_);
lean_closure_set(v___x_5808_, 3, v___x_5806_);
lean_closure_set(v___x_5808_, 4, v___x_5807_);
v___x_5809_ = l_Lean_Meta_Grind_Action_andThen(v___x_5808_, v___f_5804_, v_snd_5797_, v_kna_5780_, v_kp_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_);
return v___x_5809_;
}
v___jp_5813_:
{
if (v___y_5814_ == 0)
{
v___y_5803_ = v___x_5811_;
goto v___jp_5802_;
}
else
{
lean_object* v___x_5815_; 
v___x_5815_ = lean_nat_add(v___x_5811_, v___x_5812_);
lean_dec(v___x_5811_);
v___y_5803_ = v___x_5815_;
goto v___jp_5802_;
}
}
}
else
{
lean_object* v_snd_5817_; lean_object* v___x_5818_; 
lean_dec_ref(v_kp_5781_);
v_snd_5817_ = lean_ctor_get(v_a_5795_, 1);
lean_inc(v_snd_5817_);
lean_dec(v_a_5795_);
v___x_5818_ = lean_apply_11(v_kna_5780_, v_snd_5817_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, lean_box(0));
return v___x_5818_;
}
}
else
{
lean_object* v_a_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5826_; 
lean_dec(v_a_5790_);
lean_dec_ref(v_a_5789_);
lean_dec(v_a_5788_);
lean_dec_ref(v_a_5787_);
lean_dec(v_a_5786_);
lean_dec_ref(v_a_5785_);
lean_dec(v_a_5784_);
lean_dec_ref(v_a_5783_);
lean_dec(v_a_5782_);
lean_dec_ref(v_kp_5781_);
lean_dec_ref(v_kna_5780_);
v_a_5819_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5826_ == 0)
{
v___x_5821_ = v___x_5794_;
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_a_5819_);
lean_dec(v___x_5794_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_5827_, lean_object* v_compress_5828_, lean_object* v_goal_5829_, lean_object* v_kna_5830_, lean_object* v_kp_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5842_; uint8_t v_compress_boxed_5843_; lean_object* v_res_5844_; 
v_stopAtFirstFailure_boxed_5842_ = lean_unbox(v_stopAtFirstFailure_5827_);
v_compress_boxed_5843_ = lean_unbox(v_compress_5828_);
v_res_5844_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_5842_, v_compress_boxed_5843_, v_goal_5829_, v_kna_5830_, v_kp_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_);
return v_res_5844_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
